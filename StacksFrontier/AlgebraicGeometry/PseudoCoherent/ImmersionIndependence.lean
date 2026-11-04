module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy

/-!
# Finite type of the top cohomology sheaf of an `m`-pseudo-coherent object

Let `X` be a ringed space and let `K` be an `m`-pseudo-coherent object of the derived category of
`𝒪_X`-modules whose cohomology sheaves vanish in every degree above `m`. Stacks 08DN(1) says that
`H^m(K)` is an `𝒪_X`-module of finite type; that is the main result of this file.

`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PushforwardPseudoCoherent.lean` proves the heart of
it — that the degree-`m` cohomology sheaf of a *strictly perfect* complex with no cohomology above
`m` is of finite type, by descending through the cycles. What is left, and what this file does, is
to carry that conclusion from the open subspace on which a strictly perfect approximation of `K`
exists back to `X`, which is where finite type has to be asserted.

Together with Stacks 08CD this is what the induction of Stacks 09VA consumes: to run that
induction one must, at each stage, choose a map `𝒪^{⊕n}[-p] ⟶ E` which is a surjection on `H^p`,
and that requires `H^p(E)` to be of finite type.

## Main results

* `AlgebraicGeometry.RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom`:
  **Stacks 08DN(1)**.
* `AlgebraicGeometry.RingedSpace.exists_isDirectSummandOfFiniteFree_restrict_cycles`: the cycles
  in degree `m` of a strictly perfect complex on an open subspace `U` of `X`, with no cohomology
  above `m`, are a direct summand of a finite free module after restriction to a smaller open
  subspace of `X`.
* `AlgebraicGeometry.RingedSpace.exists_epi_free_over_of_epi_finiteFree`: an epimorphism onto the
  restriction of an `𝒪_X`-module to an open subspace, out of a finite free module, is an
  epimorphism onto its restriction to the corresponding slice, out of a free module.

## Implementation notes

Three idioms for "the modules on an open `W` of `X`" meet in this proof, and the work is in moving
between them.

* `m`-pseudo-coherence (Stacks 08CB) produces its strictly perfect approximation on the *ringed
  space* `X.restrict U.isOpenEmbedding`.
* The local argument of
  `AlgebraicGeometry.RingedSpace.exists_isDirectSummandOfFiniteFreeOver_cycles` shrinks opens, so
  it runs in the *slice* idiom, on the site of opens of that ringed space.
* `SheafOfModules.IsFiniteType` is asserted on `X` and asks for generating sections of `ℱ.over W`
  for opens `W` of `X` — the slice idiom again, but on the site of opens of `X`.

`AlgebraicGeometry.RingedSpace.restrictOverHom` is the reindexing which crosses from the second to
`AlgebraicGeometry.RingedSpace.restrictModulesOfLE` on the open subspace `W ≤ U` of `X`; it is not
a functor's action on morphisms, so the retract is transported by hand, using that it is
compatible with composition and takes restrictions of global morphisms to restrictions
(`AlgebraicGeometry.RingedSpace.retractRestrictModulesOfLE`). Crossing from there to the third
idiom is the equivalence `TopologicalSpace.Opens.sheafOfModulesEquivOver`, whose inverse is a left
adjoint and therefore preserves the epimorphism being transported; the free module it has to carry
is identified by the universal property of the coproduct defining `SheafOfModules.free`, plus the
fact that the equivalence matches the two unit sheaves of modules.

The epimorphism transported is the composite
`𝒪^{⊕n} ⟶ Z^m(𝒫) ⟶ H^m(𝒫) ⟶ H^m(E|_U) ≅ H^m(E)|_U`, restricted to `W`: the first map is the
retraction of the cycles onto a finite free module, the second is the canonical surjection onto
cohomology, the third is the approximating morphism, which is an epimorphism on `H^m` by the
definition of `m`-pseudo-coherence, and the last identification is exactness of restriction.
Restriction to a smaller open subspace preserves finite colimits, so all three survive it.

Local hypotheses of the form `Epi f` are not reliably picked up by instance synthesis in this
area, so epimorphy of a functor image is produced by applying
`CategoryTheory.Functor.PreservesEpimorphisms.preserves` with explicit arguments rather than by
`infer_instance`.

The statement is narrower than the Stacks source in one respect: the ringed space is
`RingedSpace.{u, u}`, with the universe of the rings equal to the universe of the space.
`StrictlyPerfect.OXMod`, hence `m`-pseudo-coherence as formalized in this directory, is only
defined under that identification, so no wider statement is available here. The source imposes no
such restriction. Part (2) of Stacks 08DN is proved in
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationNextCohomology`, which carries
the `"part (2)"` clause. It does not go through the truncation of Stacks aux_0556 (which is
unproved): `H^{m+1}` is the cokernel of `𝒫^m ⟶ Z^{m+1}(𝒫)`, and both terms become direct
summands of finite frees after restriction, by the same cycles lemma this file uses.

## References

* [The Stacks Project, Lemma 20.47.4 (08DN)](https://stacks.math.columbia.edu/tag/08DN)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- The cohomology of the restriction of a complex of `𝒪_X`-modules to an open subspace is the
restriction of its cohomology: restriction is exact, so it commutes with the formation of
homology of the short complex in each degree. -/
public def restrictComplexHomologyIso (E : CochainComplex (OXMod.{u, u} X) ℤ)
    (U : Opens X.carrier) (i : ℤ) :
    (restrictComplex E U).homology i ≅ (restrictModules X U).obj (E.homology i) :=
  (E.sc i).mapHomologyIso (restrictModules X U)

/-- The `i`-th cohomology of the object of the derived category represented by a complex is the
`i`-th cohomology sheaf of that complex. -/
public def derivedHomologyIso [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (E : CochainComplex (OXMod.{u, u} X) ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj (DerivedCategory.Q.obj E) ≅
      E.homology i :=
  (DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X) i).app E

/-- The equivalence between sheaves of modules over the slice `Over W` and `𝒪`-modules on the open
subspace `W` takes the unit sheaf of modules to the structure module. -/
public def equivOverUnitIso (X : RingedSpace.{u, u}) (W : Opens X.carrier) :
    SheafOfModules.unit (structureSheafOfRings (X.restrict W.isOpenEmbedding)) ≅
      (W.sheafOfModulesEquivOver (structureSheafOfRings X)).functor.obj
        (SheafOfModules.unit ((structureSheafOfRings X).over W)) :=
  (W.sheafOfModulesEquivOverUnit (structureSheafOfRings X)).symm

/-- The equivalence between sheaves of modules over the slice `Over W` and `𝒪`-modules on the open
subspace `W` takes free modules to free modules: it preserves the coproduct of copies of the unit
sheaf of modules which defines them, and matches the two units. -/
public def equivOverFreeIso (X : RingedSpace.{u, u}) (W : Opens X.carrier) (I : Type u) :
    SheafOfModules.free (R := structureSheafOfRings (X.restrict W.isOpenEmbedding)) I ≅
      (W.sheafOfModulesEquivOver (structureSheafOfRings X)).functor.obj
        (SheafOfModules.free (R := (structureSheafOfRings X).over W) I) :=
  (SheafOfModules.isColimitFreeCofan
      (R := structureSheafOfRings (X.restrict W.isOpenEmbedding)) I).coconePointsIsoOfNatIso
    (isColimitOfPreserves (W.sheafOfModulesEquivOver (structureSheafOfRings X)).functor
      (SheafOfModules.isColimitFreeCofan (R := (structureSheafOfRings X).over W) I))
    (Discrete.natIso fun _ => equivOverUnitIso X W)

/-- A functor preserving epimorphisms takes an epimorphism to an epimorphism. -/
private theorem epi_map_of_epi {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    [F.PreservesEpimorphisms] {A B : C} {f : A ⟶ B} (hf : Epi f) : Epi (F.map f) :=
  @Functor.PreservesEpimorphisms.preserves _ _ _ _ F _ _ _ f hf

/-- An epimorphism `𝒪_W^{⊕n} ⟶ ℱ|_W` of modules on the open subspace `W` of `X` gives an
epimorphism onto the restriction of `ℱ` to the slice `Over W`, out of the free sheaf of modules on
`ULift (Fin n)`.

The inverse of the equivalence `TopologicalSpace.Opens.sheafOfModulesEquivOver` is a left adjoint,
hence preserves the epimorphism; its source and target are then identified with the free sheaf of
modules and with the restriction to the slice by
`AlgebraicGeometry.RingedSpace.equivOverFreeIso`, `AlgebraicGeometry.RingedSpace.finiteFreeIsoFree`
and `AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp`. -/
public theorem exists_epi_free_over_of_epi_finiteFree (M : OXMod.{u, u} X) (W : Opens X.carrier)
    (n : ℕ) (q : finiteFree (X.restrict W.isOpenEmbedding) n ⟶ (restrictModules X W).obj M)
    (hq : Epi q) :
    ∃ p : SheafOfModules.free (R := (structureSheafOfRings X).over W) (ULift.{u} (Fin n)) ⟶
      M.over W, Epi p := by
  let EW := W.sheafOfModulesEquivOver (structureSheafOfRings X)
  have hadj : EW.inverse.IsLeftAdjoint := ⟨_, ⟨EW.symm.toAdjunction⟩⟩
  have eSrc : SheafOfModules.free (R := (structureSheafOfRings X).over W)
      (ULift.{u} (Fin n)) ≅ EW.inverse.obj (finiteFree (X.restrict W.isOpenEmbedding) n) :=
    EW.unitIso.app _ ≪≫ EW.inverse.mapIso ((equivOverFreeIso X W (ULift.{u} (Fin n))).symm ≪≫
      (finiteFreeIsoFree (X.restrict W.isOpenEmbedding) n).symm)
  have eTgt : EW.inverse.obj ((restrictModules X W).obj M) ≅ M.over W :=
    EW.inverse.mapIso ((restrictModulesIsoOverComp X W).symm.app M) ≪≫
      (EW.unitIso.app (M.over W)).symm
  refine ⟨eSrc.hom ≫ EW.inverse.map q ≫ eTgt.hom, ?_⟩
  have hmap : Epi (EW.inverse.map q) := epi_map_of_epi EW.inverse hq
  infer_instance

/-- A retract of `𝒪_U`-modules over an open `V` of the subspace `U`, read as a retract of their
restrictions to an open subspace `W ≤ U` of `X` contained in `V`.

Reindexing (`AlgebraicGeometry.RingedSpace.restrictOverHom`) is not the action on morphisms of a
functor, so the retract is transported by hand; it is compatible with composition and takes the
restriction of a global morphism to its restriction, which is all that is needed. -/
public def retractRestrictModulesOfLE {U W : Opens X.carrier} (hWU : W ≤ U)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) (hWV : ∀ p : U, p.1 ∈ W → p ∈ V)
    {A B : OXMod.{u, u} (X.restrict U.isOpenEmbedding)}
    (ρ : Retract ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj A)
      ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj B)) :
    Retract ((restrictModulesOfLE X hWU).obj A) ((restrictModulesOfLE X hWU).obj B) where
  i := restrictOverHom hWU V hWV ρ.i
  r := restrictOverHom hWU V hWV ρ.r
  retract := by
    rw [← restrictOverHom_comp, ρ.retract, ← CategoryTheory.Functor.map_id,
      restrictOverHom_map, CategoryTheory.Functor.map_id]

/-- Let `𝒫` be a strictly perfect complex of `𝒪_U`-modules on an open subspace `U` of `X` whose
cohomology sheaves vanish in every degree above `m`. Then every point of `U` has an open
neighbourhood `W ≤ U` in `X` such that the restriction of `Z^m(𝒫)` to `W` is a direct summand of a
finite free module.

This is `AlgebraicGeometry.RingedSpace.exists_isDirectSummandOfFiniteFreeOver_cycles`, applied on
the ringed space `U` where `𝒫` is defined, with its conclusion carried from the slice idiom to the
open subspace of `X` corresponding to the open of `U` it produces. -/
public theorem exists_isDirectSummandOfFiniteFree_restrict_cycles
    {U : Opens X.carrier} {P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ}
    (hP : IsStrictlyPerfect P) (m : ℤ)
    (hzero : ∀ i : ℤ, m < i → IsZero (P.homology i)) {x : X.carrier} (hxU : x ∈ U) :
    ∃ (W : Opens X.carrier) (hWU : W ≤ U), x ∈ W ∧
      IsDirectSummandOfFiniteFree ((restrictModulesOfLE X hWU).obj (P.cycles m)) := by
  obtain ⟨V, -, hyV, n, ⟨ρ⟩⟩ := exists_isDirectSummandOfFiniteFreeOver_cycles hP m hzero
    (j := m) le_rfl ⊤ (Set.mem_univ (⟨x, hxU⟩ : (X.restrict U.isOpenEmbedding).carrier))
  have hWU : (U.overEquivalence.inverse.obj V).left ≤ U :=
    leOfHom (U.overEquivalence.inverse.obj V).hom
  have hxW : x ∈ (U.overEquivalence.inverse.obj V).left := ⟨⟨x, hxU⟩, hyV, rfl⟩
  have hWV : ∀ p : U, p.1 ∈ (U.overEquivalence.inverse.obj V).left → p ∈ V := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := hp
    have : q = p := Subtype.ext hpq
    subst p
    exact hq
  obtain ⟨n', ⟨ρ'⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract _).mp
    (isDirectSummandOfFiniteFree_restrictModulesOfLE hWU
      (A := finiteFree (X.restrict U.isOpenEmbedding) n) ⟨n, ⟨Retract.refl _⟩⟩)
  exact ⟨_, hWU, hxW, (isDirectSummandOfFiniteFree_iff_retract _).mpr
    ⟨n', ⟨(retractRestrictModulesOfLE hWU V hWV ρ).trans ρ'⟩⟩⟩

/-- **Stacks 08DN, part (1).** Let `X` be a ringed space and let `K` be an `m`-pseudo-coherent
object of the derived category of `𝒪_X`-modules with `H^i(K) = 0` for `i > m`. Then `H^m(K)` is an
`𝒪_X`-module of finite type.

Finite type is a local condition, so it is enough to produce, around each point of `X`, an
epimorphism onto `H^m(K)` from a finite free module. Let `E` be a complex representing `K` which
is `m`-pseudo-coherent as a complex, and let `𝒫 ⟶ E|_U` be a strictly perfect approximation on an
open neighbourhood `U` of the given point: it is an isomorphism on cohomology above `m` and an
epimorphism in degree `m`. Since restriction is exact and `H^i(K)` vanishes above `m`, the
cohomology of `𝒫` vanishes above `m` too, so
`AlgebraicGeometry.RingedSpace.exists_isDirectSummandOfFiniteFree_restrict_cycles` makes `Z^m(𝒫)`
a direct summand of a finite free module after restriction to a smaller `W`. Composing the
retraction with `Z^m(𝒫) ⟶ H^m(𝒫) ⟶ H^m(E|_U) ≅ H^m(E)|_U` gives the required epimorphism, which
`AlgebraicGeometry.RingedSpace.exists_epi_free_over_of_epi_finiteFree` reads in the slice idiom in
which finite type is phrased. -/
@[stacks 08DN "part (1)"]
public theorem isFiniteType_homology_of_isPseudoCoherentFrom
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (K : DerivedCategory (OXMod.{u, u} X)) (m : ℤ)
    (hK : IsPseudoCoherentFrom K m)
    (hvanish : ∀ i : ℤ, m < i →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj K)) :
    SheafOfModules.IsFiniteType (R := structureSheafOfRings X)
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) m).obj K) := by
  obtain ⟨E, hE, ⟨eK⟩⟩ := hK
  have eEK : ∀ i : ℤ, E.homology i ≅
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj K := fun i =>
    (derivedHomologyIso E i).symm ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso eK
  have hvanishE : ∀ i : ℤ, m < i → IsZero (E.homology i) := fun i hi =>
    IsZero.of_iso (hvanish i hi) (eEK i)
  refine isFiniteType_of_exists_local_free_epi _ fun x => ?_
  obtain ⟨U, hxU, P, hP, α, hα, hα₀⟩ := hE x
  have hPzero : ∀ i : ℤ, m < i → IsZero (P.homology i) := fun i hi =>
    IsZero.of_iso ((restrictModules X U).isZero_obj (hvanishE i hi))
      (@asIso _ _ _ _ _ (hα i hi) ≪≫ restrictComplexHomologyIso E U i)
  obtain ⟨W, hWU, hxW, hAsummand⟩ :=
    exists_isDirectSummandOfFiniteFree_restrict_cycles hP m hPzero hxU
  obtain ⟨n, ⟨ρA⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract _).mp hAsummand
  set G := restrictModulesOfLE X hWU
  have e₁ : Epi (G.map (P.homologyπ m)) := epi_map_of_epi G inferInstance
  have e₂ : Epi (G.map (HomologicalComplex.homologyMap α m)) := epi_map_of_epi G hα₀
  have hr : Epi ρA.r := inferInstance
  obtain ⟨p, hp⟩ := exists_epi_free_over_of_epi_finiteFree
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) m).obj K) W n
    (ρA.r ≫ G.map (P.homologyπ m) ≫ G.map (HomologicalComplex.homologyMap α m) ≫
      (G.mapIso (restrictComplexHomologyIso E U m)).hom ≫
      ((restrictModulesOfLECompIso X hWU).app (E.homology m)).hom ≫
      ((restrictModules X W).mapIso (eEK m)).hom) inferInstance
  exact ⟨W, n, hxW, p, hp⟩

end AlgebraicGeometry.RingedSpace

end
