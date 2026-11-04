module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedComplex
public import StacksFrontier.Homology.PseudoCoherentRelative.TildePseudoCoherent
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# Reading a strictly perfect approximation on `Spec S` back to modules

Let `S` be a commutative ring and `M^•` a complex of `S`-modules. This file proves the affine
heart of the direction of Stacks 08E7 which goes from sheaves to modules: if the complex
`\widetilde{M^•}` of `𝒪_{Spec S}`-modules receives a map from a strictly perfect complex which
is an isomorphism on cohomology above `m` and an epimorphism in degree `m`, then `M^•` is
`m`-pseudo-coherent as a complex of `S`-modules.

## Main definitions

* `CategoryTheory.Functor.FullyFaithful.mapHomologicalComplex`: a fully faithful functor induces
  a fully faithful functor on cochain complexes.
* `Stacks.AffineTilde.tildeGammaComplexIso`: a complex of quasi-coherent `𝒪_{Spec S}`-modules is
  the complex associated to its complex of global sections.

## Main results

* `CategoryTheory.isIso_homologyMap_of_mapHomologicalComplex` and
  `CategoryTheory.epi_homologyMap_of_mapHomologicalComplex`: an exact fully faithful functor
  *reflects* the two cohomological conditions, the converse of the two transport lemmas in
  `StacksFrontier/AlgebraicGeometry/PseudoCoherent/PseudoCoherentIso.lean`.
* `CategoryTheory.Functor.epi_of_epi_map_of_faithful`: a faithful functor reflects
  epimorphisms, which Mathlib does not record as an instance.
* `StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.comp`: `m`-pseudo-coherence travels along a
  morphism which is an isomorphism on cohomology above `m` and an epimorphism in degree `m`.
* `StacksDraft.PseudoCoherence.isPseudoCoherent_of_isStrictlyLE_finiteProjective`: the direction
  of Stacks 064U used here, with the complex kept behind a variable.
* `Stacks.AffineTilde.isIso_fromTildeΓ_of_isDirectSummandOfFiniteFree` and
  `Stacks.AffineTilde.finite_and_projective_moduleSpecΓ_of_isDirectSummandOfFiniteFree`: a term
  of a strictly perfect complex on `Spec S` is quasi-coherent, with finite projective global
  sections.
* `Stacks.AffineTilde.isPseudoCoherent_moduleSpecΓ_of_isStrictlyPerfect`: the complex of global
  sections of a strictly perfect complex on `Spec S` is pseudo-coherent.
* `Stacks.AffineTilde.isPseudoCoherentFrom_of_strictlyPerfect_approximation`: the affine heart
  of the direction of Stacks 08E7 from sheaves to modules.

## Implementation note on `Stacks.AffineTilde.isPseudoCoherent_moduleSpecΓ_of_isStrictlyPerfect`

Stacks 064U is stated with its two characterizations bound by `let`, so projecting out of the
conjunction weak-head-normalizes whatever complex it is applied to. Applied directly to the
complex `(moduleSpecΓFunctor.mapHomologicalComplex _).obj 𝒫` that exhausts the heartbeat budget
(200000 heartbeats); with the complex a plain variable the whole file elaborates in
under four seconds. Hence
`StacksDraft.PseudoCoherence.isPseudoCoherent_of_isStrictlyLE_finiteProjective`, which keeps the
complex behind a variable. It has to be stated at `ModuleCat.{max u v} R`, matching Stacks 064U's
own binder: at `ModuleCat.{v} R` the universe constraint `max u ?v =?= v` is stuck.

## Implementation notes

The approximating complex `𝒫` is not assumed to be of the form `\widetilde{E^•}`; that it is,
is the first step. Each term of a strictly perfect complex on `Spec S` is a direct summand of a
finite free module, hence by the affine case of Stacks 0BCI
(`Stacks.AffineTilde.exists_finiteProjective_tilde_of_retract_finiteFree`) is `N^~` for a finite
projective `S`-module `N`; so each term is quasi-coherent, and
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ` is an isomorphism on it. Applying that degreewise —
which is legitimate because it is the component of a natural transformation,
`AlgebraicGeometry.Scheme.Modules.fromTildeΓNatTrans` — gives `\widetilde{Γ(𝒫)} ≅ 𝒫` as
complexes, with no choice of the modules `N` entering. The complex `E^• := Γ(𝒫)` then has finite
projective terms and vanishes in large degrees.

Crucially `E^•` is **not** claimed to be finite *free*; the source arranges that by shrinking the
open further, and that is not needed here. Stacks 064U
(`StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective`)
says a bounded-above complex of finite projective modules is pseudo-coherent, hence
`m`-pseudo-coherent for every `m`, and the bounded complex of finite free modules that
`StacksDraft.PseudoCoherence.IsPseudoCoherentFrom` asks for is produced by that theorem rather
than by a further localization.

The morphism of complexes of modules is obtained from fullness of `M ↦ M^~`, applied degreewise:
a fully faithful functor induces a fully faithful functor on complexes, since the commutation
with the differentials is a consequence of faithfulness. Its two cohomological properties are
read back by exactness of `M ↦ M^~`, through the natural isomorphism
`CategoryTheory.mapHomologicalComplexHomologyNatIso` already used for the forward direction:
`CategoryTheory.NatIso.isIso_map_iff` and `CategoryTheory.NatIso.epi_map_iff` are equivalences,
so only the reflection of `IsIso` and `Epi` by a fully faithful functor has to be supplied.

## References

* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 064U](https://stacks.math.columbia.edu/tag/064U)
* [Stacks Project, Tag 0BCI](https://stacks.math.columbia.edu/tag/0BCI)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

/-- A fully faithful functor between preadditive categories which preserves zero morphisms
induces a fully faithful functor on homological complexes: the preimage of a morphism of
complexes is taken degreewise, and it commutes with the differentials because the functor is
faithful. -/
def Functor.FullyFaithful.mapHomologicalComplex {V : Type u₁} [Category.{v₁} V] [Preadditive V]
    {W : Type u₂} [Category.{v₂} W] [Preadditive W] {F : V ⥤ W} (hF : F.FullyFaithful)
    [F.PreservesZeroMorphisms] {ι : Type*} (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).FullyFaithful where
  preimage {A B} f :=
    { f := fun i ↦ hF.preimage (f.f i)
      comm' := fun i j hij ↦ hF.map_injective (by
        simp only [F.map_comp, hF.map_preimage]
        exact f.comm' i j hij) }
  map_preimage {A B} f := by ext i; exact hF.map_preimage (f.f i)
  preimage_map {A B} f := by ext i; exact hF.preimage_map (f.f i)

/-- A faithful functor reflects epimorphisms. Mathlib has
`CategoryTheory.Functor.epi_of_epi_map` for a functor which is assumed to reflect
epimorphisms, and no instance deducing that from faithfulness. -/
@[sga "4 I 6.2" "(ii)"]
theorem Functor.epi_of_epi_map_of_faithful {V : Type u₁} [Category.{v₁} V] {W : Type u₂}
    [Category.{v₂} W] (F : V ⥤ W) [F.Faithful] {A B : V} {f : A ⟶ B} (h : Epi (F.map f)) :
    Epi f :=
  ⟨fun _ _ hab ↦ F.map_injective (h.left_cancellation _ _ (by
    rw [← F.map_comp, ← F.map_comp, hab]))⟩

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- An exact fully faithful functor *reflects* the property of being an isomorphism on cohomology
in a given degree. This is the converse of
`CategoryTheory.isIso_homologyMap_mapHomologicalComplex`. -/
theorem isIso_homologyMap_of_mapHomologicalComplex (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (hF : F.FullyFaithful)
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (i : ℤ)
    (hf : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) i)) :
    IsIso (HomologicalComplex.homologyMap f i) :=
  have : IsIso (F.map (HomologicalComplex.homologyMap f i)) :=
    (NatIso.isIso_map_iff (mapHomologicalComplexHomologyNatIso F i) f).mp hf
  hF.isIso_of_isIso_map _

/-- An exact fully faithful functor *reflects* the property of being an epimorphism on cohomology
in a given degree. This is the converse of
`CategoryTheory.epi_homologyMap_mapHomologicalComplex`. -/
theorem epi_homologyMap_of_mapHomologicalComplex (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Faithful]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (i : ℤ)
    (hf : Epi (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) i)) :
    Epi (HomologicalComplex.homologyMap f i) :=
  F.epi_of_epi_map_of_faithful
    ((NatIso.epi_map_iff (mapHomologicalComplexHomologyNatIso F i) f).mp hf)

end CategoryTheory

namespace StacksDraft.PseudoCoherence

universe v u

/-- `m`-pseudo-coherence travels along a morphism of `D(R)` which is an isomorphism on cohomology
in every degree above `m` and an epimorphism on cohomology in degree `m`: compose the two
approximating morphisms. -/
theorem IsPseudoCoherentFrom.comp {R : Type u} [Ring R]
    {K L : DerivedCategory (ModuleCat.{v} R)} {m : ℤ} (hK : IsPseudoCoherentFrom K m)
    (α : K ⟶ L) (hα : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map α))
    (hα₀ : Epi ((DerivedCategory.homologyFunctor _ m).map α)) : IsPseudoCoherentFrom L m := by
  obtain ⟨E, hE, β, hβ, hβ₀⟩ := hK
  refine ⟨E, hE, β ≫ α, fun i hi ↦ ?_, ?_⟩
  · have := hβ i hi
    have := hα i hi
    rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp]
    exact @epi_comp _ _ _ _ _ _ hβ₀ _ hα₀

/-- **Stacks 064U, the direction that is used here.** A bounded-above complex of finite
projective modules is pseudo-coherent.

Stated with the complex as a variable rather than inlined at the complex it is applied to:
`StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective`
states its two abbreviations with `let`, so projecting out of the conjunction has to weak-head
normalize the complex, and doing that on a complex built by applying a functor exhausts the
heartbeat budget. -/
theorem isPseudoCoherent_of_isStrictlyLE_finiteProjective {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{max u v} R) ℤ) (b : ℤ)
    (hLE : CochainComplex.IsStrictlyLE E b)
    (hfp : ∀ i : ℤ, Module.Finite R (E.X i) ∧ Module.Projective R (E.X i)) :
    IsPseudoCoherent (DerivedCategory.Q.obj E) := by
  have h := pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
    (DerivedCategory.Q.obj E) 0
  dsimp only at h
  exact h.2.1.mpr ⟨E, ⟨b, hLE⟩, hfp, ⟨Iso.refl _⟩⟩

end StacksDraft.PseudoCoherence

namespace Stacks.AffineTilde

open StacksDraft.PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

variable {S : CommRingCat.{u}}

/-- **The affine case of Stacks 0BCI, read on a single term.** A direct summand of a finite free
`𝒪_{Spec S}`-module is `N^~` for a finite projective `S`-module `N`. This is
`Stacks.AffineTilde.exists_finiteProjective_tilde_of_retract_finiteFree` with the retract
unpacked from `Stacks.StrictlyPerfect.IsDirectSummandOfFiniteFree`. -/
theorem exists_finiteProjective_tilde_of_isDirectSummandOfFiniteFree {F : (Spec S).Modules}
    (h : StrictlyPerfect.IsDirectSummandOfFiniteFree (X := (Spec S).toRingedSpace) F) :
    ∃ N : ModuleCat.{u} S, Module.Finite S N ∧ Module.Projective S N ∧
      Nonempty ((tilde.functor S).obj N ≅ F) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract F).mp h
  exact exists_finiteProjective_tilde_of_retract_finiteFree ρ

/-- A term of a strictly perfect complex on `Spec S` is quasi-coherent: it is a direct summand of
a finite free `𝒪_{Spec S}`-module, hence `N^~` for a finite projective `S`-module `N` by the
affine case of Stacks 0BCI. -/
theorem isIso_fromTildeΓ_of_isDirectSummandOfFiniteFree {F : (Spec S).Modules}
    (h : StrictlyPerfect.IsDirectSummandOfFiniteFree
      (X := (Spec S).toRingedSpace) F) :
    IsIso (Scheme.Modules.fromTildeΓ F) := by
  obtain ⟨N, -, -, ⟨e⟩⟩ := exists_finiteProjective_tilde_of_isDirectSummandOfFiniteFree h
  rw [isIso_fromTildeΓ_iff]
  exact ⟨N, ⟨e⟩⟩

/-- The global sections of a term of a strictly perfect complex on `Spec S` form a finite
projective `S`-module: the term is `N^~` for such an `N` by the affine case of Stacks 0BCI, and
global sections of `N^~` are `N` by the unit of the tilde–`Γ` adjunction. -/
theorem finite_and_projective_moduleSpecΓ_of_isDirectSummandOfFiniteFree
    {F : (Spec S).Modules} (h : StrictlyPerfect.IsDirectSummandOfFiniteFree
      (X := (Spec S).toRingedSpace) F) :
    Module.Finite S (moduleSpecΓFunctor.obj F) ∧
      Module.Projective S (moduleSpecΓFunctor.obj F) := by
  obtain ⟨N, hfin, hproj, ⟨e⟩⟩ := exists_finiteProjective_tilde_of_isDirectSummandOfFiniteFree h
  have hiso : N ≅ moduleSpecΓFunctor.obj F :=
    tilde.toTildeΓNatIso.app N ≪≫ moduleSpecΓFunctor.mapIso e
  exact ⟨Module.Finite.equiv hiso.toLinearEquiv,
    Module.Projective.of_equiv' hiso.toLinearEquiv⟩

/-- Taking global sections of `𝒪_{Spec S}`-modules is additive: it is the right adjoint of
`M ↦ M^~`, so it preserves limits, hence binary products, hence binary biproducts. -/
instance additive_moduleSpecΓFunctor : (moduleSpecΓFunctor (R := S)).Additive :=
  have := (tilde.adjunction (R := S)).rightAdjoint_preservesLimits
  have : PreservesBinaryBiproducts (moduleSpecΓFunctor (R := S)) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- A complex of quasi-coherent `𝒪_{Spec S}`-modules is the complex associated to its complex of
global sections: the counit of the tilde–`Γ` adjunction is a morphism of complexes, because it is
a natural transformation, and it is an isomorphism in every degree. -/
def tildeGammaComplexIso (P : CochainComplex (Spec S).Modules ℤ)
    (hP : ∀ i : ℤ, IsIso (Scheme.Modules.fromTildeΓ (P.X i))) :
    ((tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((moduleSpecΓFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅ P :=
  haveI (i : ℤ) : IsIso (((NatTrans.mapHomologicalComplex
      (Scheme.Modules.fromTildeΓNatTrans (R := S)) (ComplexShape.up ℤ)).app P).f i) := hP i
  haveI := HomologicalComplex.Hom.isIso_of_components ((NatTrans.mapHomologicalComplex
    (Scheme.Modules.fromTildeΓNatTrans (R := S)) (ComplexShape.up ℤ)).app P)
  asIso ((NatTrans.mapHomologicalComplex
    (Scheme.Modules.fromTildeΓNatTrans (R := S)) (ComplexShape.up ℤ)).app P)

/-- A strictly perfect complex on `Spec S` vanishes in all sufficiently large degrees, and so
does its complex of global sections. -/
theorem exists_isStrictlyLE_moduleSpecΓ_of_isStrictlyPerfect
    (P : CochainComplex (Spec S).Modules ℤ)
    (hP : StrictlyPerfect.IsStrictlyPerfect (X := (Spec S).toRingedSpace) P) :
    ∃ b : ℤ, CochainComplex.IsStrictlyLE
      ((moduleSpecΓFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) b := by
  obtain ⟨b, hb⟩ := hP.bounded.bddAbove
  refine ⟨b, (CochainComplex.isStrictlyLE_iff
    ((moduleSpecΓFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) b).2 fun i hi ↦ ?_⟩
  refine moduleSpecΓFunctor.map_isZero ?_
  by_contra hz
  exact absurd (hb (show i ∈ {j : ℤ | ¬ IsZero (P.X j)} from hz)) (by omega)

/-- **The complex of global sections of a strictly perfect complex on `Spec S` is
pseudo-coherent.** It is bounded above and its terms are finite projective `S`-modules, so
Stacks 064U applies. -/
theorem isPseudoCoherent_moduleSpecΓ_of_isStrictlyPerfect
    (P : CochainComplex (Spec S).Modules ℤ)
    (hP : StrictlyPerfect.IsStrictlyPerfect (X := (Spec S).toRingedSpace) P) :
    IsPseudoCoherent (DerivedCategory.Q.obj
      ((moduleSpecΓFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  (exists_isStrictlyLE_moduleSpecΓ_of_isStrictlyPerfect P hP).elim fun b hb ↦
    isPseudoCoherent_of_isStrictlyLE_finiteProjective _ b hb fun i ↦
      finite_and_projective_moduleSpecΓ_of_isDirectSummandOfFiniteFree (hP.directSummand i)

/-- A morphism from a strictly perfect complex on `Spec S` to `\widetilde{M^•}` comes from a
morphism of complexes of `S`-modules out of the complex of global sections, by fullness of
`M ↦ M^~`, and that morphism inherits the two cohomological properties by exactness and
faithfulness. -/
theorem exists_hom_moduleSpecΓ_of_strictlyPerfect_approximation
    (M : CochainComplex (ModuleCat.{u} S) ℤ) (m : ℤ)
    (P : CochainComplex (Spec S).Modules ℤ)
    (hqc : ∀ i : ℤ, IsIso (Scheme.Modules.fromTildeΓ (P.X i)))
    (β : P ⟶ tildeComplex M)
    (hβ : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j))
    (hβ₀ : Epi (HomologicalComplex.homologyMap β m)) :
    ∃ γ : (moduleSpecΓFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ M,
      (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap γ j)) ∧
        Epi (HomologicalComplex.homologyMap γ m) := by
  have hex₁ := AlgebraicGeometry.tilde.preservesFiniteLimits S
  have hex₂ := preservesFiniteColimits_tildeFunctor S
  obtain ⟨γ, hγ⟩ : ∃ γ : (moduleSpecΓFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ M,
      ((tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ)).map γ =
        (tildeGammaComplexIso P hqc).hom ≫ β :=
    ⟨_, ((tilde.fullyFaithfulFunctor (R := S)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map_preimage _⟩
  refine ⟨γ, fun j hj ↦ isIso_homologyMap_of_mapHomologicalComplex (tilde.functor S)
    (tilde.fullyFaithfulFunctor (R := S)) γ j ?_,
    epi_homologyMap_of_mapHomologicalComplex (tilde.functor S) γ m ?_⟩
  · rw [hγ]
    exact isIso_homologyMap_comp _ _ j (isIso_homologyMap_iso_hom _ j) (hβ j hj)
  · rw [hγ]
    exact epi_homologyMap_comp _ _ m (epi_homologyMap_iso_hom _ m) hβ₀

/-- **The affine heart of Stacks 08E7, from sheaves to modules.** If the complex
`\widetilde{M^•}` of `𝒪_{Spec S}`-modules associated to a complex `M^•` of `S`-modules receives a
morphism from a strictly perfect complex which is an isomorphism on cohomology in every degree
above `m` and an epimorphism on cohomology in degree `m`, then `M^•` is `m`-pseudo-coherent as a
complex of `S`-modules.

No further shrinking of the base is involved: the approximating complex is identified with
`\widetilde{E^•}` for a bounded-above complex `E^•` of finite *projective* `S`-modules, which is
pseudo-coherent by Stacks 064U, and the bounded complex of finite free modules required by
`StacksDraft.PseudoCoherence.IsPseudoCoherentFrom` is produced from that. -/
theorem isPseudoCoherentFrom_of_strictlyPerfect_approximation
    (M : CochainComplex (ModuleCat.{u} S) ℤ) (m : ℤ)
    (P : CochainComplex (Spec S).Modules ℤ)
    (hP : StrictlyPerfect.IsStrictlyPerfect (X := (Spec S).toRingedSpace) P)
    (β : P ⟶ tildeComplex M)
    (hβ : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j))
    (hβ₀ : Epi (HomologicalComplex.homologyMap β m)) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj M) m := by
  obtain ⟨γ, hγ₁, hγ₂⟩ := exists_hom_moduleSpecΓ_of_strictlyPerfect_approximation M m P
    (fun i ↦ isIso_fromTildeΓ_of_isDirectSummandOfFiniteFree (hP.directSummand i)) β hβ hβ₀
  exact ((pseudoCoherent_iff_all _).1
    (isPseudoCoherent_moduleSpecΓ_of_isStrictlyPerfect P hP) m).comp (DerivedCategory.Q.map γ)
    (fun j hj ↦ isIso_homologyFunctor_map_Q_map γ j (hγ₁ j hj))
    (epi_homologyFunctor_map_Q_map γ m hγ₂)

end Stacks.AffineTilde

end
