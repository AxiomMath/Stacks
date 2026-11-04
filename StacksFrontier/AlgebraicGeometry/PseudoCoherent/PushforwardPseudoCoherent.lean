module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectHomotopyGlobal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas

/-!
# The cycles of a strictly perfect complex with no high cohomology, and finite generation

Let `X` be a ringed space and let `𝒫` be a strictly perfect complex of `𝒪_X`-modules whose
cohomology sheaves vanish in every degree above `m`. This file proves that the cycles `Z^j(𝒫)`
are, locally on `X`, direct summands of finite free modules for every `j ≥ m`, and deduces that
`H^m(𝒫)` is an `𝒪_X`-module of finite type.

This is the content of Stacks 08DN(1) — the lemma that the top possibly nonzero cohomology sheaf
of an `m`-pseudo-coherent object is of finite type. Indeed the source proof reduces at once to the
case of a strictly perfect complex ("It suffices to prove the result for `ℰ^•`"), because the
approximating morphism of Stacks 08CB is a surjection on `H^m` and finite type passes to
quotients; the remaining work, done here, is entirely about a strictly perfect complex. Stacks
08DN(1) itself needs, in addition, the transfer of the conclusion from the open subspace carrying
the strictly perfect approximation back to `X`; that transfer is not performed here.

Stacks 08DN is, with Stacks 08CD, what the induction of Stacks 09VA (`Ri_*E` is
`m`-pseudo-coherent iff `E` is, for a closed immersion of ringed spaces with pseudo-coherent
`i_*𝒪_Z`) consumes: at each step of that induction one needs `H^p(E)` to be of finite type in
order to choose a map `𝒪_Z^{⊕n}[-p] ⟶ E` which is a surjection on `H^p`, and
`AlgebraicGeometry.RingedSpace.exists_epi_free_over_homology` is exactly the local datum from
which such a map is built.

## Main definitions

* `AlgebraicGeometry.RingedSpace.IsDirectSummandOfFiniteFreeOver`: an `𝒪_X`-module is a direct
  summand of a finite free module *over an open subset* `W`, i.e. its restriction to the slice
  `Over W` of the site of opens is a retract of the restriction of some `𝒪_X^{⊕n}`.
* `AlgebraicGeometry.RingedSpace.localGeneratorsDataOfLocalFreeEpi`: the local generators of an
  `𝒪_X`-module presented by a family of epimorphisms from free modules over a family of opens
  covering `X`.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_isDirectSummandOfFiniteFreeOver_cycles`: for a strictly
  perfect complex with vanishing cohomology above `m`, and for `j ≥ m`, the cycles `Z^j` are
  locally direct summands of finite free modules.
* `AlgebraicGeometry.RingedSpace.exists_epi_free_over_homology`: `H^m` of such a complex is,
  locally on `X`, a quotient of a finite free module.
* `AlgebraicGeometry.RingedSpace.isFiniteType_homology_of_isStrictlyPerfect`: `H^m` of such a
  complex is an `𝒪_X`-module of finite type.

## Implementation notes

The source proves the finite generation of `H^m` by an induction which *modifies the complex*:
if `n > m` is the top degree in which `𝒫` is nonzero then `𝒫^{n-1} ⟶ 𝒫^n` is a surjection, which
Stacks 08C6 splits locally, and one replaces `𝒫^{n-1}` by the kernel of that surjection and `𝒫^n`
by zero. The induction here runs over the same local splittings but never builds a new complex:
it descends through the *cycles*, which already exist as objects. Concretely, vanishing of
`H^{j+1}(𝒫)` says that `𝒫^j ⟶ Z^{j+1}(𝒫)` is an epimorphism; granted that `Z^{j+1}(𝒫)` is a direct
summand of a finite free module over `W`, Stacks 08C6 over an open subset
(`AlgebraicGeometry.RingedSpace.exists_local_lift_over_of_isDirectSummandOfFiniteFree`) splits it
over a smaller `W'`, and the complementary idempotent `𝟙 - 𝒫^j ⟶ Z^{j+1} ⟶ 𝒫^j` factors through
`Z^j(𝒫)` and exhibits it as a retract of `𝒫^j`, hence of a finite free module. The induction
terminates because `𝒫` vanishes in high degrees, where the cycles vanish too; it is phrased as an
induction on a natural number bounding the distance from that vanishing range.

Everything local happens in the slice idiom: the opens `W' ≤ W` are opens of `X`, so shrinking is
`SheafOfModules.overRestrict` and no ringed space other than `X` enters. This is the same reason
Stacks 08C6, 08C7 and 08C8 are phrased in that idiom in this directory. The lifting lemma requires
the epimorphism it splits to be a *global* morphism on `X`, which `𝒫^j ⟶ Z^{j+1}(𝒫)` is; only the
section is local.

Restriction to a slice is the pushforward of sheaves of modules along the identity morphism of
sheaves of rings, hence a left adjoint
(`AlgebraicGeometry.RingedSpace.overFunctor_isLeftAdjoint`); that is what makes it preserve
epimorphisms, which is used to push `Z^m(𝒫) ⟶ H^m(𝒫)` into the slice.

`SheafOfModules.IsFiniteType` asks for local generators indexed by a type in the universe of the
site, so the covering used is indexed by the points of `X` themselves. Its witness is assembled
through the auxiliary `AlgebraicGeometry.RingedSpace.localGeneratorsDataOfLocalFreeEpi` rather
than inline, because the index universe of `SheafOfModules.LocalGeneratorsData` has to be pinned
before the existential is introduced.

All universes coincide, as everywhere in this directory: `StrictlyPerfect.OXMod` is only defined
when the ring universe and the space universe of the ringed space agree.

## References

* [The Stacks Project, Lemma 20.47.4 (08DN)](https://stacks.math.columbia.edu/tag/08DN)
* [The Stacks Project, Lemma 20.46.3 (08C6)](https://stacks.math.columbia.edu/tag/08C6)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect

namespace CochainComplex

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- The inclusion of the cycles in degree `j` is killed by the map to the cycles in degree
`j + 1`: after composing with the monomorphism `Z^{j+1} ⟶ K^{j+1}` it becomes the composite of
the inclusion `Z^j ⟶ K^j` with the differential, which is zero. -/
public theorem iCycles_comp_toCycles (K : CochainComplex C ℤ) (j : ℤ) :
    K.iCycles j ≫ K.toCycles j (j + 1) = 0 := by
  rw [← cancel_mono (K.iCycles (j + 1)), Category.assoc, HomologicalComplex.toCycles_i,
    HomologicalComplex.iCycles_d, Limits.zero_comp]

/-- If a complex vanishes in degree `j` then so do its cycles in degree `j`: the inclusion of the
cycles is a monomorphism into a zero object, so the identity of the cycles is zero. -/
public theorem isZero_cycles_of_isZero_X (K : CochainComplex C ℤ) (j : ℤ) (h : IsZero (K.X j)) :
    IsZero (K.cycles j) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (K.iCycles j), Category.id_comp, Limits.zero_comp]
  exact h.eq_of_tgt _ _

end CochainComplex

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}}

/-- Restriction of sheaves of modules to the slice `Over W` of the site of opens of a ringed space
is a left adjoint: it is the pushforward along the identity morphism of sheaves of rings.

Spelling this out is what lets typeclass resolution see that restriction to a slice preserves
finite colimits, and in particular epimorphisms; the two descriptions of the functor are
definitionally but not reducibly equal, so the instance is not found on its own. -/
public instance overFunctor_isLeftAdjoint (X : RingedSpace.{u, u}) (W : Opens X.carrier) :
    (SheafOfModules.overFunctor.{u} (structureSheafOfRings X) W).IsLeftAdjoint :=
  inferInstanceAs (SheafOfModules.pushforward.{u}
    (𝟙 ((structureSheafOfRings X).over W))).IsLeftAdjoint

/-- An `𝒪_X`-module is a *direct summand of a finite free module over the open subset `W`* if its
restriction to the slice `Over W` of the site of opens of `X` is a retract of the restriction of
`𝒪_X^{⊕n}` for some `n`.

This is `StrictlyPerfect.IsDirectSummandOfFiniteFree` read over an open subset, in the slice
idiom: the ambient ringed space stays `X`, so the opens over which the property is asserted can be
shrunk without changing spaces. -/
public def IsDirectSummandOfFiniteFreeOver (A : OXMod.{u, u} X) (W : Opens X.carrier) : Prop :=
  ∃ n : ℕ, Nonempty (Retract (A.over W) ((finiteFree X n).over W))

/-- A zero `𝒪_X`-module is a direct summand of a finite free module over every open subset: its
restriction is zero, and a zero object is a retract of `𝒪_X^{⊕0}` through the zero morphisms. -/
public theorem isDirectSummandOfFiniteFreeOver_of_isZero {A : OXMod.{u, u} X} (h : IsZero A)
    (W : Opens X.carrier) : IsDirectSummandOfFiniteFreeOver A W :=
  ⟨0, ⟨⟨0, 0, by
    rw [Limits.zero_comp]
    exact ((IsZero.iff_id_eq_zero _).mp
      ((SheafOfModules.overFunctor (structureSheafOfRings X) W).isZero_obj h)).symm⟩⟩⟩

/-- A strictly perfect complex of `𝒪_X`-modules vanishes in every degree above some integer,
since only finitely many of its terms are nonzero.

This is the upper counterpart of `Stacks.Cohomology.LocalNullHomotopy.exists_lower_bound`,
and it
is what makes the descending induction on the cycles terminate. -/
public theorem exists_forall_gt_isZero {E : CochainComplex (OXMod.{u, u} X) ℤ}
    (hE : IsStrictlyPerfect E) : ∃ b : ℤ, ∀ p : ℤ, b < p → IsZero (E.X p) := by
  obtain ⟨b, hb⟩ : BddAbove {i : ℤ | ¬ IsZero (E.X i)} := hE.bounded.bddAbove
  exact ⟨b, fun p hp => not_not.mp fun hp' => absurd (hb hp') (not_le.mpr hp)⟩

/-- One step of the descending induction on the cycles of a strictly perfect complex. Let `𝒫` be
strictly perfect with `H^{j+1}(𝒫) = 0`, and suppose `Z^{j+1}(𝒫)` is a direct summand of a finite
free module over an open subset `W`. Then every point of `W` has a smaller open neighbourhood over
which `Z^j(𝒫)` is a direct summand of a finite free module.

Vanishing of `H^{j+1}(𝒫)` makes `𝒫^j ⟶ Z^{j+1}(𝒫)` an epimorphism
(`AlgebraicGeometry.RingedSpace.epi_toCycles_of_isZero_homology`). Applying Stacks 08C6 over an
open subset to the retraction `𝒪_X^{⊕n}|_W ⟶ Z^{j+1}(𝒫)|_W` and composing with the section of that
retract produces, over a smaller `W'`, a morphism `σ : Z^{j+1}(𝒫)|_{W'} ⟶ 𝒫^j|_{W'}` with
`σ ≫ (𝒫^j ⟶ Z^{j+1}(𝒫))|_{W'} = 𝟙`. The complementary endomorphism `𝟙 - (𝒫^j ⟶ Z^{j+1}) ≫ σ` of
`𝒫^j|_{W'}` is killed by the differential, so it factors through `Z^j(𝒫)|_{W'}` — restriction to a
slice preserves finite limits, hence carries the kernel fork defining the cycles to a kernel fork
— and the factorisation is a retraction of the inclusion `Z^j(𝒫)|_{W'} ⟶ 𝒫^j|_{W'}` because
`Z^j(𝒫) ⟶ 𝒫^j ⟶ Z^{j+1}(𝒫)` is zero. Composing with the retract witnessing that `𝒫^j` is a direct
summand of a finite free module finishes the step. -/
public theorem exists_isDirectSummandOfFiniteFreeOver_cycles_succ
    {P : CochainComplex (OXMod.{u, u} X) ℤ} (hP : IsStrictlyPerfect P) {j : ℤ}
    (hzero : IsZero (P.homology (j + 1))) (W : Opens X.carrier)
    (hW : IsDirectSummandOfFiniteFreeOver (P.cycles (j + 1)) W)
    {x : X.carrier} (hx : x ∈ W) :
    ∃ W' : Opens X.carrier, W' ≤ W ∧ x ∈ W' ∧
      IsDirectSummandOfFiniteFreeOver (P.cycles j) W' := by
  obtain ⟨n, ⟨ρ⟩⟩ := hW
  have : Epi (P.toCycles j (j + 1)) := epi_toCycles_of_isZero_homology rfl hzero
  obtain ⟨W', hW'W, hxW', l, hl⟩ := exists_local_lift_over_of_isDirectSummandOfFiniteFree
    (E := finiteFree X n) (P.toCycles j (j + 1)) ⟨n, ⟨Retract.refl _⟩⟩ W ρ.r hx
  set F := SheafOfModules.overFunctor.{u} (structureSheafOfRings X) W'
  set σ : (P.cycles (j + 1)).over W' ⟶ (P.X j).over W' :=
    SheafOfModules.overRestrict (homOfLE hW'W) ρ.i ≫ l with hσdef
  have hσ : σ ≫ F.map (P.toCycles j (j + 1)) = 𝟙 _ := by
    rw [hσdef, Category.assoc, hl, ← SheafOfModules.overRestrict_comp, ρ.retract]
    exact SheafOfModules.overRestrict_map (homOfLE hW'W) (𝟙 _)
  have hker : IsLimit ((KernelFork.ofι (P.iCycles j) (P.iCycles_d j (j + 1))).map F) :=
    KernelFork.mapIsLimit _ (P.cyclesIsKernel j (j + 1) (by simp)) _
  have hd : F.map (P.d j (j + 1)) =
      F.map (P.toCycles j (j + 1)) ≫ F.map (P.iCycles (j + 1)) := by
    rw [← F.map_comp, HomologicalComplex.toCycles_i]
  have hzz : (𝟙 ((P.X j).over W') - F.map (P.toCycles j (j + 1)) ≫ σ) ≫
      F.map (P.d j (j + 1)) = 0 := by
    rw [hd, Preadditive.sub_comp, Category.id_comp, Category.assoc, ← Category.assoc σ,
      hσ, Category.id_comp, sub_self]
  obtain ⟨r, hr⟩ := KernelFork.IsLimit.lift' hker _ hzz
  simp only [KernelFork.map_ι, Fork.ι_ofι] at hr
  obtain ⟨nj, ⟨ρj⟩⟩ :=
    (isDirectSummandOfFiniteFree_iff_retract _).mp (hP.directSummand j)
  refine ⟨W', hW'W, hxW', nj, ⟨Retract.trans ⟨F.map (P.iCycles j), r, ?_⟩ (ρj.map F)⟩⟩
  refine Fork.IsLimit.hom_ext hker ?_
  simp only [KernelFork.map_ι, Fork.ι_ofι]
  rw [Category.assoc, hr, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ← F.map_comp,
    CochainComplex.iCycles_comp_toCycles, F.map_zero, Limits.zero_comp, sub_zero,
    Category.id_comp]

/-- Let `𝒫` be a strictly perfect complex of `𝒪_X`-modules whose cohomology sheaves vanish in
every degree above `m`. Then for every `j ≥ m` and every open `W` containing a point `x`, the
cycles `Z^j(𝒫)` are a direct summand of a finite free module over some smaller open neighbourhood
of `x`.

The induction descends from a degree `b` above which `𝒫` vanishes, where the cycles vanish as
well, to `j`, one application of
`AlgebraicGeometry.RingedSpace.exists_isDirectSummandOfFiniteFreeOver_cycles_succ` per degree; the
opens shrink at each step and the number of steps is finite, which is what the induction on
`(b + 1 - j).toNat` records. -/
public theorem exists_isDirectSummandOfFiniteFreeOver_cycles
    {P : CochainComplex (OXMod.{u, u} X) ℤ} (hP : IsStrictlyPerfect P) (m : ℤ)
    (hzero : ∀ i : ℤ, m < i → IsZero (P.homology i)) {j : ℤ} (hmj : m ≤ j)
    (W : Opens X.carrier) {x : X.carrier} (hx : x ∈ W) :
    ∃ W' : Opens X.carrier, W' ≤ W ∧ x ∈ W' ∧
      IsDirectSummandOfFiniteFreeOver (P.cycles j) W' := by
  obtain ⟨b, hb⟩ := exists_forall_gt_isZero hP
  suffices H : ∀ k : ℕ, ∀ j : ℤ, m ≤ j → b + 1 - j ≤ (k : ℤ) →
      ∀ W : Opens X.carrier, x ∈ W → ∃ W' : Opens X.carrier, W' ≤ W ∧ x ∈ W' ∧
        IsDirectSummandOfFiniteFreeOver (P.cycles j) W' from
    H (b + 1 - j).toNat j hmj (Int.self_le_toNat _) W hx
  intro k
  induction k with
  | zero =>
    intro j _ hk W hxW
    exact ⟨W, le_rfl, hxW, isDirectSummandOfFiniteFreeOver_of_isZero
      (CochainComplex.isZero_cycles_of_isZero_X P j (hb j (by omega))) W⟩
  | succ k ih =>
    intro j hmj hk W hxW
    by_cases hle : b + 1 - j ≤ (k : ℤ)
    · exact ih j hmj hle W hxW
    · obtain ⟨W₁, hW₁, hxW₁, h₁⟩ := ih (j + 1) (by omega) (by push_cast at hk ⊢; omega) W hxW
      obtain ⟨W', hW'W₁, hxW', h'⟩ := exists_isDirectSummandOfFiniteFreeOver_cycles_succ hP
        (hzero (j + 1) (by omega)) W₁ h₁ hxW₁
      exact ⟨W', hW'W₁.trans hW₁, hxW', h'⟩

/-- The free sheaf of modules on `ULift (Fin n)` over the slice `Over W`, identified with the
`n`-fold biproduct of the unit sheaf of modules: a finite coproduct is a biproduct, and the index
types are reindexed by `Equiv.ulift`.

The `ULift` is forced by `SheafOfModules.free`, which indexes free modules by types in the
universe of the sheaf of rings. -/
public def freeOverBiproductIso (X : RingedSpace.{u, u}) (W : Opens X.carrier) (n : ℕ) :
    SheafOfModules.free (R := (structureSheafOfRings X).over W) (ULift.{u} (Fin n)) ≅
      ⨁ fun _ : Fin n => SheafOfModules.unit ((structureSheafOfRings X).over W) :=
  (biproduct.isoCoproduct (fun _ : ULift.{u} (Fin n) =>
      SheafOfModules.unit ((structureSheafOfRings X).over W))).symm ≪≫
    biproduct.whiskerEquiv (g := fun _ : Fin n =>
      SheafOfModules.unit ((structureSheafOfRings X).over W)) Equiv.ulift (fun _ => Iso.refl _)

/-- The restriction of `𝒪_X^{⊕n}` to the slice `Over W` is a retract of the `n`-fold biproduct of
the unit sheaf of modules over `Over W`.

One does not need restriction to *preserve* the biproduct: it is additive, so the two biproduct
comparison morphisms compose to the identity (`CategoryTheory.Functor.retractMapBiproduct`), and
it takes the unit sheaf of modules to the unit sheaf of modules over the slice
(`SheafOfModules.overUnitIso`). -/
public def finiteFreeOverRetract (X : RingedSpace.{u, u}) (W : Opens X.carrier) (n : ℕ) :
    Retract ((finiteFree X n).over W)
      (⨁ fun _ : Fin n => SheafOfModules.unit ((structureSheafOfRings X).over W)) :=
  ((SheafOfModules.overFunctor (structureSheafOfRings X) W).retractMapBiproduct
      fun _ : Fin n => structureModule X).trans
    (Retract.ofIso (biproduct.mapIso fun _ : Fin n =>
      SheafOfModules.overUnitIso (structureSheafOfRings X) W))

/-- Let `𝒫` be a strictly perfect complex of `𝒪_X`-modules whose cohomology sheaves vanish in
every degree above `m`. Then every point of `X` has an open neighbourhood `W` over which `H^m(𝒫)`
is a quotient of a finite free module.

The cycles `Z^m(𝒫)` are a direct summand of a finite free module over such a `W`, and
`Z^m(𝒫) ⟶ H^m(𝒫)` is an epimorphism which stays one after restriction to the slice, restriction
being a left adjoint. -/
public theorem exists_epi_free_over_homology {P : CochainComplex (OXMod.{u, u} X) ℤ}
    (hP : IsStrictlyPerfect P) (m : ℤ) (hzero : ∀ i : ℤ, m < i → IsZero (P.homology i))
    (x : X.carrier) :
    ∃ (W : Opens X.carrier) (n : ℕ), x ∈ W ∧
      ∃ p : SheafOfModules.free (R := (structureSheafOfRings X).over W) (ULift.{u} (Fin n)) ⟶
        (P.homology m).over W, Epi p := by
  obtain ⟨W, -, hxW, n, ⟨ρ⟩⟩ :=
    exists_isDirectSummandOfFiniteFreeOver_cycles hP m hzero le_rfl ⊤ (Set.mem_univ x)
  refine ⟨W, n, hxW, (freeOverBiproductIso X W n).hom ≫ (finiteFreeOverRetract X W n).r ≫ ρ.r ≫
    (SheafOfModules.overFunctor (structureSheafOfRings X) W).map (P.homologyπ m), ?_⟩
  have h₁ : Epi (finiteFreeOverRetract X W n).r := inferInstance
  have h₂ : Epi ρ.r := inferInstance
  infer_instance

/-- The local generators of an `𝒪_X`-module `ℱ` presented, over an open neighbourhood `W x` of
each point `x` of `X`, by an epimorphism from a free module on `ULift (Fin (n x))`.

The covering of `X` is indexed by the points of `X` themselves, which is the only index type in
the universe of the site that is available without further choices; the opens `W x` cover `X`
because each contains its own point. -/
public def localGeneratorsDataOfLocalFreeEpi (M : OXMod.{u, u} X)
    (W : X.carrier → Opens X.carrier) (hxW : ∀ x, x ∈ W x) (n : X.carrier → ℕ)
    (p : ∀ x : X.carrier, SheafOfModules.free (R := (structureSheafOfRings X).over (W x))
      (ULift.{u} (Fin (n x))) ⟶ M.over (W x)) (hp : ∀ x, Epi (p x)) :
    SheafOfModules.LocalGeneratorsData.{u} M where
  I := (X.carrier : Type u)
  X := W
  coversTop := (Opens.coversTop_iff (X.carrier : Type u) W).mpr
    (TopologicalSpace.IsOpenCover.mk
      (Opens.ext (Set.eq_univ_of_forall fun x => (Opens.mem_iSup (s := W)).2 ⟨x, hxW x⟩)))
  generators x :=
    have := hp x
    (SheafOfModules.free.generatingSections (ULift.{u} (Fin (n x)))).ofEpi (p x)

/-- The local generators of `AlgebraicGeometry.RingedSpace.localGeneratorsDataOfLocalFreeEpi` are
of finite type: over each open of the covering they are the images of the tautological generating
sections of a free module on a finite index type. -/
public instance isFiniteType_localGeneratorsDataOfLocalFreeEpi (M : OXMod.{u, u} X)
    (W : X.carrier → Opens X.carrier) (hxW : ∀ x, x ∈ W x) (n : X.carrier → ℕ)
    (p : ∀ x : X.carrier, SheafOfModules.free (R := (structureSheafOfRings X).over (W x))
      (ULift.{u} (Fin (n x))) ⟶ M.over (W x)) (hp : ∀ x, Epi (p x)) :
    (localGeneratorsDataOfLocalFreeEpi M W hxW n p hp).IsFiniteType where
  isFiniteType x := by
    have := hp x
    have : (SheafOfModules.free.generatingSections
      (R := (structureSheafOfRings X).over (W x)) (ULift.{u} (Fin (n x)))).IsFiniteType :=
      ⟨inferInstanceAs (Finite (ULift.{u} (Fin (n x))))⟩
    exact inferInstanceAs (((SheafOfModules.free.generatingSections
      (ULift.{u} (Fin (n x)))).ofEpi (p x)).IsFiniteType)

/-- An `𝒪_X`-module which is, locally on `X`, a quotient of a finite free module is of finite
type. -/
public theorem isFiniteType_of_exists_local_free_epi (M : OXMod.{u, u} X)
    (h : ∀ x : X.carrier, ∃ (W : Opens X.carrier) (n : ℕ), x ∈ W ∧
      ∃ q : SheafOfModules.free (R := (structureSheafOfRings X).over W) (ULift.{u} (Fin n)) ⟶
        M.over W, Epi q) :
    SheafOfModules.IsFiniteType (R := structureSheafOfRings X) M := by
  classical
  choose W n hxW p hp using h
  constructor
  exact ⟨localGeneratorsDataOfLocalFreeEpi M W hxW n p hp,
    isFiniteType_localGeneratorsDataOfLocalFreeEpi M W hxW n p hp⟩

/-- **The strictly perfect case of Stacks 08DN(1).** Let `𝒫` be a strictly perfect complex of
`𝒪_X`-modules whose cohomology sheaves vanish in every degree above `m`. Then `H^m(𝒫)` is an
`𝒪_X`-module of finite type.

This is the whole content of Stacks 08DN(1): there the complex is only locally available, and the
argument runs on the open subspace carrying it, with the surjection of the approximating morphism
on `H^m` transporting finite generation to the given object. -/
public theorem isFiniteType_homology_of_isStrictlyPerfect
    {P : CochainComplex (OXMod.{u, u} X) ℤ} (hP : IsStrictlyPerfect P) (m : ℤ)
    (hzero : ∀ i : ℤ, m < i → IsZero (P.homology i)) :
    SheafOfModules.IsFiniteType (R := structureSheafOfRings X) (P.homology m) :=
  isFiniteType_of_exists_local_free_epi _ (exists_epi_free_over_homology hP m hzero)

end AlgebraicGeometry.RingedSpace

end
