module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericConstancy
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import StacksFrontier.Topology.Constructible.InConstructible
public import StacksFrontier.Topology.Constructible.NormalForm
public import StacksFrontier.Topology.Noetherian.ConstructibleDichotomy
public import StacksFrontier.Algebra.Category.Ring.FiniteSubalgebras

/-!
# Local constructibility of the level sets of the dimension of the fibres

For a morphism of schemes of finite presentation, each level set
`E_n = {y | n_{X/Y}(y) = n}` of the dimension-of-fibres function is locally constructible in the
target.

The proof is the source's. The question is local on the target, so the target may be assumed
affine, say `Spec A`; writing `A` as the filtered colimit of its finite-type `ℤ`-subalgebras and
descending `f` to a finite stage (Tag 01ZM) reduces, by the base-change formula for the
dimension-of-fibres function (Tag 05F8) and the stability of local constructibility under inverse
image (Tag 054I), to a Noetherian target. There the criterion of Tag 053Z applies: on an
irreducible closed subset the dimension of the fibres is constant near the generic point by
Tag 05F7, so the level set either contains a nonempty open subset of that closed subset or misses
a neighbourhood of its generic point and so is not dense in it.

## Main results

* `AlgebraicGeometry.isLocallyConstructible_fiberDimension_eq` is **Stacks Tag 05F9**: every
  level set of `AlgebraicGeometry.Scheme.Hom.fiberDimension` is locally constructible.

## Implementation notes

The level is an arbitrary element of `WithBot ℕ∞`, so the statement also covers the level `⊥` of
the points with empty fibre and the level `⊤` of the points with infinite-dimensional fibre.

The reduction to the Noetherian case needs the target to be the spectrum of a ring, so that its
ring of functions can be written as a filtered colimit of finite-type `ℤ`-algebras; the step from
an affine target to the spectrum of a ring is the base-change formula along
`AlgebraicGeometry.Scheme.isoSpec`, which is an isomorphism and hence gives a pullback square
with two parallel isomorphisms.

The dichotomy of Tag 053Z is stated for the explicit description `IsConstructibleSet` of a
constructible set as a finite union of differences of retrocompact opens, so
`isConstructibleSet_of_isConstructible` converts Mathlib's `Topology.IsConstructible` into it
where the dichotomy is applied to the image of `f`.

## References

* [Stacks Project, Tag 05F9](https://stacks.math.columbia.edu/tag/05F9)
* [Stacks Project, Tag 05F7](https://stacks.math.columbia.edu/tag/05F7)
* [Stacks Project, Tag 05F8](https://stacks.math.columbia.edu/tag/05F8)
* [Stacks Project, Tag 053Z](https://stacks.math.columbia.edu/tag/053Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set.Notation Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism of finite presentation to the spectrum of a ring is the base change of a morphism
of finite presentation to the spectrum of a finite-type `ℤ`-algebra, which is a Noetherian
scheme. -/
private theorem exists_noetherianSpace_model {X : Scheme.{u}} (R : CommRingCat.{u}) (f : X ⟶ Spec R)
    (hf : FinitePresentation f) :
    ∃ (Y₀ X₀ : Scheme.{u}) (g : Spec R ⟶ Y₀) (f₀ : X₀ ⟶ Y₀),
      NoetherianSpace Y₀ ∧ FinitePresentation f₀ ∧
      Nonempty (Over.mk f ≅ (Over.pullback g).obj (Over.mk f₀)) := by
  let D := R.finiteSubalgebras.op ⋙ Scheme.Spec
  let c := Scheme.Spec.mapCone R.finiteSubalgebrasCocone.op
  have hc : IsLimit c := isLimitOfPreserves _ R.finiteSubalgebrasIsColimit.op
  have : ∀ i, IsAffine (D.obj i) := fun i ↦ inferInstanceAs (IsAffine (Spec _))
  obtain ⟨i, Xi, hXi, e⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc (Over.mk f) hf
  refine ⟨D.obj i, Xi.left, c.π.app i, Xi.hom, ?_, hXi, e⟩
  have : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (i.unop : Set R)) :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
  have := Algebra.FiniteType.isNoetherianRing ℤ (Algebra.adjoin ℤ (i.unop : Set R))
  show NoetherianSpace (Spec (CommRingCat.of (Algebra.adjoin ℤ (i.unop : Set R))))
  infer_instance

/-- A generic point of a subset is a generic point of the whole of the corresponding subspace. -/
private lemma isGenericPoint_univ_subtype {T : Type*} [TopologicalSpace T] {s : Set T} {x : T}
    (hx : IsGenericPoint x s) : IsGenericPoint (⟨x, hx.mem⟩ : s) Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro y
  rw [subtype_specializes_iff, hx.specializes_iff_mem]
  simp

/-- On an irreducible closed subset of a Noetherian target on whose generic point the fibre is
empty, the dimension of the fibres is constant on a nonempty open subset, because the image of the
morphism is constructible and not dense on that subset. -/
private theorem exists_opens_fiberDimension_eq_of_isIrreducible_of_eq_bot {X Y : Scheme.{u}}
    (f : X ⟶ Y) [NoetherianSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] (Z : Set Y)
    (hZ : IsIrreducible Z) (hZclosed : IsClosed Z) (η : Y) (hη : IsGenericPoint η Z)
    (hbot : f.fiberDimension η = ⊥) :
    ∃ V : Opens Z, (V : Set Z).Nonempty ∧
      ∀ z : V, f.fiberDimension z.1.1 = f.fiberDimension η := by
  classical
  have : LocallyOfFiniteType f := inferInstance
  have himgLoc : IsLocallyConstructible (Set.range f) := by
    simpa using f.isLocallyConstructible_image IsLocallyConstructible.univ
  have himg : IsConstructible (Set.range f) := himgLoc.isConstructible
  have hηnotImg : η ∉ Set.range f := by
    rintro ⟨x, hx⟩
    have : IsEmpty (f.fiber η) := (f.fiberDimension_eq_bot_iff_isEmpty η).mp hbot
    exact isEmptyElim (hx ▸ f.asFiber x : f.fiber η)
  have hnotDense : ¬ IsDenseIn (Set.range f) Z := by
    intro hdense
    rcases (constructible_iff_dichotomy_irreducible_closed (Set.range f)).mp
      (isConstructibleSet_of_isConstructible himg) Z hZ hZclosed with
      hopen | hnotdense
    · obtain ⟨U, hU, ⟨z, hzU, hzZ⟩, hzsub⟩ := hopen
      exact hηnotImg (hzsub ⟨(hη.specializes hzZ).mem_open hU hzU, hη.mem⟩).1
    · exact hnotdense hdense
  obtain ⟨z, hzZ, hznot⟩ := Set.not_subset.mp (by simpa [IsDenseIn] using hnotDense)
  let V : Opens Z := ⟨{x | (x : Y) ∉ closure (Set.range f ∩ Z)},
    (isClosed_closure.preimage continuous_subtype_val).isOpen_compl⟩
  refine ⟨V, ⟨⟨z, hzZ⟩, hznot⟩, fun w ↦ ?_⟩
  have hwEmpty : IsEmpty (f.fiber w.1.1) := by
    refine ⟨fun q ↦ w.2 (subset_closure ⟨⟨f.fiberι w.1.1 q, ?_⟩, w.1.2⟩)⟩
    exact (f.range_fiberι w.1.1).subset ⟨q, rfl⟩
  rw [(f.fiberDimension_eq_bot_iff_isEmpty w.1.1).2 hwEmpty, hbot]

/-- On an irreducible closed subset of a Noetherian target on whose generic point the fibre has
finite dimension `n`, the dimension of the fibres is constant on a nonempty open subset: this is
Tag 05F7 applied to the base change along the reduced induced closed subscheme. -/
private theorem exists_opens_fiberDimension_eq_of_isIrreducible_of_eq_natCast {X Y : Scheme.{u}}
    (f : X ⟶ Y) [NoetherianSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] (Z : Set Y)
    (hZ : IsIrreducible Z) (hZclosed : IsClosed Z) (η : Y) (hη : IsGenericPoint η Z) (n : ℕ)
    (hcast : f.fiberDimension η = (n : WithBot ℕ∞)) :
    ∃ V : Opens Z, (V : Set Z).Nonempty ∧
      ∀ z : V, f.fiberDimension z.1.1 = f.fiberDimension η := by
  classical
  have : LocallyOfFiniteType f := inferInstance
  let I : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZclosed⟩
  have hrange : Set.range I.subschemeι = Z := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨Z, hZclosed⟩]
    rfl
  let e : I.subscheme ≃ₜ Z :=
    I.subschemeι.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hval : ∀ x : I.subscheme, (e x).1 = I.subschemeι x := fun x ↦ by
    show (I.subschemeι.isEmbedding.toHomeomorph x).1 = I.subschemeι x
    simp
  have : IrreducibleSpace I.subscheme := e.irreducibleSpace_iff.2 (Subtype.irreducibleSpace hZ)
  let ηI : I.subscheme := e.symm ⟨η, hη.mem⟩
  have hηI_val : I.subschemeι ηI = η := (hval ηI).symm.trans
    (congrArg Subtype.val (e.apply_symm_apply ⟨η, hη.mem⟩))
  have hηI : IsGenericPoint ηI Set.univ := by
    rw [isGenericPoint_iff_specializes]
    refine fun x ↦ ⟨fun _ ↦ Set.mem_univ _, fun _ ↦ ?_⟩
    rw [← e.isInducing.specializes_iff, e.apply_symm_apply]
    exact (isGenericPoint_univ_subtype hη).specializes (Set.mem_univ _)
  let fZ := pullback.snd f I.subschemeι
  have hdimη : fZ.fiberDimension ηI = f.fiberDimension η := by
    simpa [fZ, hηI_val] using congrFun (Scheme.Hom.fiberDimension_pullback_snd f I.subschemeι) ηI
  have : LocallyOfFiniteType fZ := inferInstance
  have : QuasiCompact fZ := inferInstance
  obtain ⟨VZ, hVZne, hVZ⟩ := exists_nonempty_open_fiberDimension_eq fZ n ηI hηI
    (by rw [hdimη, hcast])
  refine ⟨⟨e '' (VZ : Set I.subscheme), e.isOpenMap _ VZ.2⟩, hVZne.image e, fun z ↦ ?_⟩
  obtain ⟨x, hx, hxz⟩ := z.2
  calc f.fiberDimension z.1.1 = f.fiberDimension (I.subschemeι x) := by rw [← hval x, hxz]
    _ = fZ.fiberDimension x :=
      (congrFun (Scheme.Hom.fiberDimension_pullback_snd f I.subschemeι) x).symm
    _ = (n : WithBot ℕ∞) := hVZ x hx
    _ = f.fiberDimension η := hcast.symm

/-- On an irreducible closed subset of a Noetherian target the dimension of the fibres is constant
on a nonempty open subset: if the generic fibre is empty this is because the image of the morphism
is constructible and not dense on that subset, and otherwise it is Tag 05F7 applied to the base
change along the reduced induced closed subscheme. -/
private theorem exists_opens_fiberDimension_eq_of_isIrreducible {X Y : Scheme.{u}} (f : X ⟶ Y)
    [NoetherianSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] (Z : Set Y) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (η : Y) (hη : IsGenericPoint η Z) :
    ∃ V : Opens Z, (V : Set Z).Nonempty ∧
      ∀ z : V, f.fiberDimension z.1.1 = f.fiberDimension η := by
  classical
  have : LocallyOfFiniteType f := inferInstance
  by_cases hbot : f.fiberDimension η = ⊥
  · -- The generic fibre is empty, so the image of `f` is not dense on `Z`.
    exact exists_opens_fiberDimension_eq_of_isIrreducible_of_eq_bot f Z hZ hZclosed η hη hbot
  -- The generic fibre is nonempty of finite dimension, so Tag 05F7 applies.
  obtain ⟨N, hN⟩ := exists_topologicalKrullDim_fiber_le f
  obtain ⟨n, hcast⟩ : ∃ n : ℕ, f.fiberDimension η = (n : WithBot ℕ∞) := by
    cases hd : f.fiberDimension η with
    | bot => exact (hbot hd).elim
    | coe d =>
      have hle : f.fiberDimension η ≤ (N : WithBot ℕ∞) := hN η
      rw [hd] at hle
      obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top N)
        (WithBot.coe_le_coe.mp hle))
      exact ⟨n, by norm_cast⟩
  exact exists_opens_fiberDimension_eq_of_isIrreducible_of_eq_natCast f Z hZ hZclosed η hη n hcast

/-- Tag 05F9 for a target that is the spectrum of a ring: descend to a Noetherian target and
apply the dichotomy. -/
@[ega "IV 9.2.6.1" "Case S = Spec(A)", sga "3 VIB 4.1" "(ii)"]
private theorem isLocallyConstructible_fiberDimension_eq_spec {X : Scheme.{u}}
    (R : CommRingCat.{u}) (f : X ⟶ Spec R) (hf : FinitePresentation f) (n : WithBot ℕ∞) :
    IsLocallyConstructible {y | f.fiberDimension y = n} := by
  obtain ⟨Y₀, X₀, g, f₀, hY₀, hf₀, ⟨e⟩⟩ := exists_noetherianSpace_model R f hf
  have : NoetherianSpace Y₀ := hY₀
  obtain ⟨_, _, _⟩ := hf₀
  have h := (isConstructible_of_constant_near_genericPoints f₀.fiberDimension (fun y ↦ by
    obtain ⟨V, hV, hconst⟩ := exists_opens_fiberDimension_eq_of_isIrreducible f₀
      (closure ({y} : Set Y₀)) isIrreducible_singleton.closure isClosed_closure y
      isGenericPoint_closure
    exact ⟨V, hV.to_subtype, f₀.fiberDimension y, hconst⟩) n
    ).isLocallyConstructible
  have he := Scheme.Hom.fiberDimension_eq_of_over_iso e
  change f.fiberDimension = (pullback.snd f₀ g).fiberDimension at he
  rw [he, Scheme.Hom.fiberDimension_pullback_snd]
  exact isLocallyConstructible_preimage g h

/-- The dimension-of-fibres function of a morphism composed with an isomorphism of the target is
the original function read through the inverse isomorphism: a square with two parallel
isomorphisms is a pullback square. -/
private lemma fiberDimension_comp_iso {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (i : Y ≅ Y')
    [LocallyOfFiniteType f] : (f ≫ i.hom).fiberDimension = f.fiberDimension ∘ i.inv :=
  Scheme.Hom.fiberDimension_eq_of_isPullback
    (IsPullback.of_horiz_isIso (⟨by simp⟩ : CommSq (𝟙 X) (f ≫ i.hom) f i.inv))

/-- Tag 05F9 for an affine target: transport along `AlgebraicGeometry.Scheme.isoSpec`, which is
an isomorphism, to the spectrum of a ring. -/
@[ega "IV 9.2.6.1" "Case of an affine base S", sga "3 VIB 4.1" "(ii)"]
private theorem isLocallyConstructible_fiberDimension_eq_of_isAffine {X Y : Scheme.{u}}
    [IsAffine Y] (f : X ⟶ Y) (hf : FinitePresentation f) (n : WithBot ℕ∞) :
    IsLocallyConstructible {y : Y | f.fiberDimension y = n} := by
  obtain ⟨_, _, _⟩ := hf
  have h := (isLocallyConstructible_fiberDimension_eq_spec _ (f ≫ Y.isoSpec.hom)
    ⟨inferInstance, inferInstance, inferInstance⟩ n).preimage_of_isOpenEmbedding
    (Scheme.Hom.isOpenEmbedding Y.isoSpec.hom)
  have hinv : ∀ y : Y, Y.isoSpec.inv (Y.isoSpec.hom y) = y :=
    (Scheme.homeoOfIso Y.isoSpec).symm_apply_apply
  have hset : Y.isoSpec.hom ⁻¹' {y | (f ≫ Y.isoSpec.hom).fiberDimension y = n} =
      {y : Y | f.fiberDimension y = n} := by
    rw [fiberDimension_comp_iso f Y.isoSpec]
    ext y
    show f.fiberDimension (Y.isoSpec.inv (Y.isoSpec.hom y)) = n ↔ f.fiberDimension y = n
    rw [hinv y]
  rwa [hset] at h

/-- **Stacks Project, Tag 05F9.** For a morphism of schemes of finite presentation, every level
set of the dimension-of-fibres function is locally constructible in the target. -/
@[stacks 05F9, ega "IV 9.2.6.1", ega "IV 9.5.5" "Z = X, max dimension", sga "3 VIB 4.1" "(ii)"]
public theorem isLocallyConstructible_fiberDimension_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : FinitePresentation f) (n : WithBot ℕ∞) :
    IsLocallyConstructible {y : Y | f.fiberDimension y = n} := by
  obtain ⟨_, _, _⟩ := hf
  refine IsLocallyConstructible.of_isOpenCover Y.affineCover.isOpenCover_opensRange fun i ↦ ?_
  have : IsAffine (Y.affineCover.f i).opensRange.toScheme :=
    isAffineOpen_opensRange (Y.affineCover.f i)
  have h := isLocallyConstructible_fiberDimension_eq_of_isAffine
    (pullback.snd f (Y.affineCover.f i).opensRange.ι)
    ⟨inferInstance, inferInstance, inferInstance⟩ n
  have hset : {z : (Y.affineCover.f i).opensRange.toScheme |
        (pullback.snd f (Y.affineCover.f i).opensRange.ι).fiberDimension z = n} =
      ((Y.affineCover.f i).opensRange : Set Y) ↓∩ {y : Y | f.fiberDimension y = n} := by
    rw [Scheme.Hom.fiberDimension_pullback_snd f (Y.affineCover.f i).opensRange.ι]
    rfl
  rwa [← hset]

end AlgebraicGeometry

end
