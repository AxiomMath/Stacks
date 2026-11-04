module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineClosedSubspaceExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceSquareGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Extending finitely presented closed subspaces from quasi-compact opens

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`.  A finitely
presented closed subspace of a quasi-compact open subspace of `X` is the restriction of a finitely
presented closed subspace of `X`; more generally a finite family of such, compatible on the
overlaps, is the family of restrictions of one.  This is the closed-subspace form of Stacks 0853
for the structure sheaf: through Stacks 084Q a closed subspace of finite presentation is the same
as one cut out by a finite type quasi-coherent sheaf of ideals.

## Main results

* `AlgebraicGeometry.Space.ExtendsClosedSubspaces`: the extension property for a finite family.
* `AlgebraicGeometry.Space.ExtendsClosedSubspaces.of_isElementaryDistinguishedSquare`: the
  property crosses an elementary distinguished square with affine étale member.
* `AlgebraicGeometry.Space.extendsClosedSubspaces_of_isQuasiCompactSpace`: every quasi-compact
  and quasi-separated algebraic space has it.
* `AlgebraicGeometry.Space.exists_closedSubspace_extension_disjoint`: the form used by
  Stacks 086D — a finitely presented closed subspace of `V` avoiding `U ∩ V` extends to one of
  `X` avoiding `U`.

## Implementation notes

The source proves Stacks 0853 from Stacks 0829, whose proof for algebraic spaces rests on
Noetherian approximation (Stacks 07V9).  Here the extension is proved instead by the induction
principle of Stacks 08GP, `AlgebraicGeometry.Space.qcqs_induction_on_self`, with three inputs:
the affine case, where the statement is Stacks 01PF for a sheaf of ideals on an affine scheme
(`AlgebraicGeometry.Space.exists_closedSubspace_extension_of_isAffineSpace`); glueing of closed
subspaces along an elementary distinguished square (`AlgebraicGeometry.Space.squareGlue`, with
`AlgebraicGeometry.Space.isClosedSubspace_squareGlue` and
`AlgebraicGeometry.Space.isFinitePresentation_squareGlue`); and the fact that two subspaces
agreeing on both members of such a square agree
(`AlgebraicGeometry.Space.le_of_isElementaryDistinguishedSquare`).  The family version
is what makes the induction go through: on the affine member of a square the restrictions of the
given family and the extension already found on the open member have to be extended together.

A closed subspace `T` of an open subspace `U ⊆ Y` is recorded as a subfunctor `T ≤ U` of `Y`
whose restriction `T.preimage U.ι` is a closed subspace of `U`; compatibility on overlaps is then
the lattice identity `Tᵢ ⊓ Uⱼ = Tⱼ ⊓ Uᵢ`, and restriction of `T' ⊆ Y` to `U` is `T' ⊓ U`.

## References

* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Restricting a closed subspace of an open subspace -/

section Restrict

variable {B S hS} {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Restricting `T ⊆ Ω ⊆ F` along `g : F' ⟶ F`, read inside the preimage of `Ω`, is the
preimage of `T ⊆ Ω` along the induced map of preimages. -/
theorem preimage_preimage_ι_eq (T Ω : Subfunctor F) (g : F' ⟶ F) :
    (T.preimage g).preimage (Ω.preimage g).ι = (T.preimage Ω.ι).preimage (Ω.fromPreimage g) := by
  rw [← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp, Subfunctor.fromPreimage_ι]

variable (B S hS)

/-- The preimage of an open subspace along a morphism of algebraic spaces is an algebraic
space. -/
theorem isAlgebraicSpace_preimage_toFunctor (hF : IsAlgebraicSpace B S hS F)
    (hF' : IsAlgebraicSpace B S hS F') (Ω : Subfunctor F)
    (hΩ : IsAlgebraicSpace B S hS Ω.toFunctor) (g : F' ⟶ F) :
    IsAlgebraicSpace B S hS (Ω.preimage g).toFunctor :=
  AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS (Subfunctor.isPullback_preimage g Ω).isoPullback
    (isAlgebraicSpace_pullback B S hS Ω.ι g hΩ hF' hF)

/-- Closedness of `T ⊆ Ω` is inherited by its restriction along any morphism. -/
theorem isClosedSubspace_preimage_preimage_ι (hF : IsAlgebraicSpace B S hS F)
    (hF' : IsAlgebraicSpace B S hS F') (T Ω : Subfunctor F)
    (hΩ : IsAlgebraicSpace B S hS Ω.toFunctor) (g : F' ⟶ F)
    (hT : IsClosedSubspace B S hS (T.preimage Ω.ι)) :
    IsClosedSubspace B S hS ((T.preimage g).preimage (Ω.preimage g).ι) := by
  rw [preimage_preimage_ι_eq]
  exact isClosedSubspace_preimage B S hS _ _ hΩ
    (isAlgebraicSpace_preimage_toFunctor B S hS hF hF' Ω hΩ g) hT

/-- Finite presentation of `T ⊆ Ω` is inherited by its restriction along any morphism. -/
theorem isFinitePresentation_preimage_preimage_ι (hF : IsAlgebraicSpace B S hS F)
    (hF' : IsAlgebraicSpace B S hS F') (T Ω : Subfunctor F)
    (hΩ : IsAlgebraicSpace B S hS Ω.toFunctor) (g : F' ⟶ F)
    (hT : IsClosedSubspace B S hS (T.preimage Ω.ι))
    (hTf : IsFinitePresentation B S hS (T.preimage Ω.ι).ι) :
    IsFinitePresentation B S hS ((T.preimage g).preimage (Ω.preimage g).ι).ι := by
  rw [preimage_preimage_ι_eq]
  have hΩ' := isAlgebraicSpace_preimage_toFunctor B S hS hF hF' Ω hΩ g
  have hsq := Subfunctor.isPullback_preimage (Ω.fromPreimage g) (T.preimage Ω.ι)
  exact isFinitePresentation_of_isPullback B S hS
    (isClosedSubspace_preimage B S hS _ _ hΩ hΩ' hT).1 hT.1 hΩ' hΩ hsq hTf

/-- The preimage of a quasi-compact open subspace of a quasi-separated algebraic space along a
morphism from a quasi-compact algebraic space is quasi-compact. -/
theorem isQuasiCompactSpace_preimage_toFunctor (hZ : B.Contains (⊤_ Scheme.{u}))
    (hF : IsAlgebraicSpace B S hS F) (hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (hF' : IsAlgebraicSpace B S hS F') (hF'qc : IsQuasiCompactSpace B S hS F')
    (Ω : Subfunctor F) (hΩqc : IsQuasiCompactSpace B S hS Ω.toFunctor) (g : F' ⟶ F) :
    IsQuasiCompactSpace B S hS (Ω.preimage g).toFunctor := by
  have hqc := isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hF hFqs hΩqc Ω.ι F' hF' hF'qc g
  exact IsQuasiCompactSpace.of_iso B S hS hqc
    ((pullbackSymmetry g Ω.ι).trans (Subfunctor.isPullback_preimage g Ω).isoPullback.symm)

end Restrict

/-! ### Subfunctors of an open subspace, read in the ambient space -/

section Lattice

variable {C : Type*} [Category C] {F F' : C ⥤ Type u}

/-- Preimage of subfunctors commutes with intersection. -/
theorem preimage_inf_eq (A A' : Subfunctor F) (g : F' ⟶ F) :
    (A ⊓ A').preimage g = A.preimage g ⊓ A'.preimage g := rfl

/-- A subfunctor of `Ω` is recovered from its image in the ambient functor. -/
theorem preimage_ι_image_ι (Ω : Subfunctor F) (T : Subfunctor Ω.toFunctor) :
    (T.image Ω.ι).preimage Ω.ι = T := by
  ext U x
  simp only [Subfunctor.preimage_obj, Subfunctor.image_obj, Set.mem_preimage, Set.mem_image,
    Subfunctor.ι_app]
  refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
  rintro ⟨y, hy, hyx⟩
  have : y = x := Subtype.ext (by simpa using hyx)
  exact this ▸ hy

/-- Restricting `A ⊓ Ω` to `Ω` is restricting `A` to `Ω`. -/
private theorem preimage_inf_ι_eq (Ω A : Subfunctor F) :
    (A ⊓ Ω).preimage Ω.ι = A.preimage Ω.ι := by
  have : Ω.preimage Ω.ι = ⊤ := by rw [Subfunctor.preimage_eq_top_iff, Subfunctor.range_ι]
  rw [preimage_inf_eq, this, inf_top_eq]

/-- The image of a subfunctor of `Ω` lies in `Ω`. -/
theorem image_ι_le (Ω : Subfunctor F) (T : Subfunctor Ω.toFunctor) : T.image Ω.ι ≤ Ω := by
  rintro U _ ⟨y, -, rfl⟩
  exact y.2

/-- The image in the ambient functor of the restriction of `A` to `Ω` is `A ⊓ Ω`. -/
theorem image_ι_preimage_ι (Ω A : Subfunctor F) : (A.preimage Ω.ι).image Ω.ι = A ⊓ Ω := by
  ext U x
  simp only [Subfunctor.image_obj, Subfunctor.preimage_obj, Set.mem_image, Set.mem_preimage,
    Subfunctor.ι_app, Subfunctor.min_obj, Set.mem_inter_iff]
  refine ⟨?_, fun ⟨hA, hΩ⟩ => ⟨⟨x, hΩ⟩, hA, rfl⟩⟩
  rintro ⟨y, hy, rfl⟩
  exact ⟨hy, y.2⟩

/-- Intersecting inside `Ω` and then taking images is intersecting the images. -/
theorem image_ι_inf_preimage_ι (Ω A : Subfunctor F) (T : Subfunctor Ω.toFunctor) :
    (T ⊓ A.preimage Ω.ι).image Ω.ι = T.image Ω.ι ⊓ A := by
  ext U x
  simp only [Subfunctor.image_obj, Subfunctor.min_obj, Subfunctor.preimage_obj, Set.mem_image,
    Set.mem_inter_iff, Set.mem_preimage, Subfunctor.ι_app]
  constructor
  · rintro ⟨y, ⟨hy, hyA⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hyA⟩
  · rintro ⟨⟨y, hy, rfl⟩, hyA⟩
    exact ⟨y, ⟨hy, hyA⟩, rfl⟩

/-- For `A ≤ Ω`, the subfunctor `A` of `F` and its restriction to `Ω` are isomorphic. -/
@[simps!]
def toFunctorIsoPreimageι {Ω A : Subfunctor F} (h : A ≤ Ω) :
    A.toFunctor ≅ (A.preimage Ω.ι).toFunctor :=
  NatIso.ofComponents (fun U => Equiv.toIso
    { toFun := fun x => ⟨⟨x.1, h U x.2⟩, x.2⟩
      invFun := fun x => ⟨x.1.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })

end Lattice

/-! ### The extension property -/

/-- An algebraic space `Y` *extends finitely presented closed subspaces from quasi-compact
opens* when every finite family `Tᵢ ⊆ Uᵢ` of finitely presented closed subspaces of
quasi-compact open subspaces of `Y`, compatible on the overlaps, is the restriction of one
finitely presented closed subspace of `Y`. -/
def ExtendsClosedSubspaces (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (ι : Type) [Finite ι] (U : ι → Subfunctor Y), (∀ i, IsOpenSubspace B S hS (U i)) →
    (∀ i, IsQuasiCompactSpace B S hS (U i).toFunctor) →
    ∀ T : ι → Subfunctor Y, (∀ i, T i ≤ U i) →
      (∀ i, IsClosedSubspace B S hS ((T i).preimage (U i).ι)) →
      (∀ i, IsFinitePresentation B S hS ((T i).preimage (U i).ι).ι) →
      (∀ i j, T i ⊓ U j = T j ⊓ U i) →
      ∃ T' : Subfunctor Y, IsClosedSubspace B S hS T' ∧ IsFinitePresentation B S hS T'.ι ∧
        ∀ i, T' ⊓ U i = T i

variable {B S hS}

/-- For `A ≤ Ω`, the subfunctor `A` is an algebraic space as soon as its restriction to `Ω` is. -/
theorem isAlgebraicSpace_toFunctor_of_le {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Ω A : Subfunctor F} (h : A ≤ Ω)
    (hA : IsAlgebraicSpace B S hS (A.preimage Ω.ι).toFunctor) :
    IsAlgebraicSpace B S hS A.toFunctor :=
  AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS (toFunctorIsoPreimageι h) hA

/-- Two subfunctors of `W`, the second a sheaf, which agree on the open member of an
elementary distinguished square and after pullback to its étale member are contained in one
another. -/
theorem le_of_inf_eq_of_preimage_eq_of_isElementaryDistinguishedSquare
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    {U₀ : Subfunctor W} {f : V ⟶ W} (h : IsElementaryDistinguishedSquare B S hS hW U₀ f)
    {A A' : Subfunctor W} (hA' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A'.toFunctor)
    (h₀ : A ⊓ U₀ = A' ⊓ U₀) (h₂ : A.preimage f = A'.preimage f) : A ≤ A' :=
  le_of_isElementaryDistinguishedSquare hW h (𝟙 W) hW.isSheaf hA'
    (fun Y y hy hyU => (le_of_eq h₀ (Opposite.op Y) ⟨hy, hyU⟩).1)
    (fun Y y v hy hv => by
      have hv' : v ∈ (A.preimage f).obj (Opposite.op Y) := by
        change f.app (Opposite.op Y) v ∈ A.obj (Opposite.op Y)
        rw [hv]; exact hy
      rw [h₂] at hv'
      change f.app (Opposite.op Y) v ∈ A'.obj (Opposite.op Y) at hv'
      rw [hv] at hv'
      exact hv')

/-- **The induction step.** Let `(U₀ ⊂ W, f : V ⟶ W)` be an elementary distinguished square
with `W` quasi-separated, `U₀` quasi-compact and `V` affine.  If `U₀` extends finitely
presented closed subspaces from quasi-compact opens, so does `W`.

A compatible family `Tᵢ ⊆ Uᵢ` on `W` is restricted to `U₀` and extended there to `T₀ ⊆ U₀`;
the restrictions of the `Tᵢ` and of `T₀` to `V` form a compatible family on the affine `V`,
which extends to `T₂ ⊆ V`; and `T₀` and `T₂` glue along the square to `T ⊆ W`.  That `T`
restricts to `Tᵢ` on `Uᵢ` is checked after restriction to `U₀` and pullback to `V`. -/
theorem ExtendsClosedSubspaces.of_isElementaryDistinguishedSquare
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W)
    (U₀ : Subfunctor W) (f : V ⟶ W) (h : IsElementaryDistinguishedSquare B S hS hW U₀ f)
    (hU₀qc : IsQuasiCompactSpace B S hS U₀.toFunctor) (hVa : IsAffineSpace B S hS V)
    (hU₀ : ExtendsClosedSubspaces B S hS U₀.toFunctor) :
    ExtendsClosedSubspaces B S hS W := by
  intro ι _ U hU hUqc T hTU hTc hTf hcompat
  have hV : IsAlgebraicSpace B S hS V := h.isAlgebraicSpace
  have hU₀a : IsAlgebraicSpace B S hS U₀.toFunctor := h.isOpenSubspace.1
  have hUa : ∀ i, IsAlgebraicSpace B S hS (U i).toFunctor := fun i => (hU i).1
  -- extend the restriction of the family to `U₀`
  obtain ⟨T₀, hT₀c, hT₀f, hT₀⟩ := hU₀ ι (fun i => (U i).preimage U₀.ι)
    (fun i => isOpenSubspace_preimage B S hS U₀.ι (U i) hW hU₀a (hU i))
    (fun i => isQuasiCompactSpace_preimage_toFunctor B S hS hZ hW hWqs hU₀a hU₀qc (U i)
      (hUqc i) U₀.ι)
    (fun i => (T i).preimage U₀.ι) (fun i V x hx => hTU i V hx)
    (fun i => isClosedSubspace_preimage_preimage_ι B S hS hW hU₀a (T i) (U i) (hUa i) U₀.ι
      (hTc i))
    (fun i => isFinitePresentation_preimage_preimage_ι B S hS hW hU₀a (T i) (U i) (hUa i) U₀.ι
      (hTc i) (hTf i))
    (fun i j => congrArg (·.preimage U₀.ι) (hcompat i j))
  set T₀' : Subfunctor W := T₀.image U₀.ι with hT₀'def
  have hT₀'le : T₀' ≤ U₀ := image_ι_le U₀ T₀
  have hT₀'pre : T₀'.preimage U₀.ι = T₀ := preimage_ι_image_ι U₀ T₀
  have hT₀'inf : ∀ i, T₀' ⊓ U i = T i ⊓ U₀ := fun i => by
    rw [hT₀'def, ← image_ι_inf_preimage_ι, hT₀ i, image_ι_preimage_ι]
  -- the family on the affine `V`
  let UV : Option ι → Subfunctor V := fun o => o.elim (U₀.preimage f) (fun i => (U i).preimage f)
  let TV : Option ι → Subfunctor V := fun o => o.elim (T₀'.preimage f) (fun i => (T i).preimage f)
  have hVqc : IsQuasiCompactSpace B S hS V := hVa.isQuasiCompactSpace
  obtain ⟨T₂, hT₂c, hT₂f, hT₂⟩ := exists_closedSubspace_extension_of_isAffineSpace B S hS hV hVa UV
    (fun o => match o with
      | none => isOpenSubspace_preimage B S hS f U₀ hW hV h.isOpenSubspace
      | some i => isOpenSubspace_preimage B S hS f (U i) hW hV (hU i))
    (fun o => match o with
      | none => isQuasiCompactSpace_preimage_toFunctor B S hS hZ hW hWqs hV hVqc U₀ hU₀qc f
      | some i => isQuasiCompactSpace_preimage_toFunctor B S hS hZ hW hWqs hV hVqc (U i)
          (hUqc i) f)
    TV
    (fun o => match o with
      | none => fun V x hx => hT₀'le V hx
      | some i => fun V x hx => hTU i V hx)
    (fun o => match o with
      | none => isClosedSubspace_preimage_preimage_ι B S hS hW hV T₀' U₀ hU₀a f
          (hT₀'pre ▸ hT₀c)
      | some i => isClosedSubspace_preimage_preimage_ι B S hS hW hV (T i) (U i) (hUa i) f
          (hTc i))
    (fun o => match o with
      | none => isFinitePresentation_preimage_preimage_ι B S hS hW hV T₀' U₀ hU₀a f
          (hT₀'pre ▸ hT₀c) (hT₀'pre ▸ hT₀f)
      | some i => isFinitePresentation_preimage_preimage_ι B S hS hW hV (T i) (U i) (hUa i) f
          (hTc i) (hTf i))
    (fun o o' => match o, o' with
      | none, none => rfl
      | none, some j => congrArg (·.preimage f) (hT₀'inf j)
      | some i, none => congrArg (·.preimage f) (hT₀'inf i).symm
      | some i, some j => congrArg (·.preimage f) (hcompat i j))
  -- glue `T₀` and `T₂` along the square
  have hcomp : ∀ (Y : BigFppfOver B S hS) (a : U₀.toFunctor.obj (Opposite.op Y))
      (b : V.obj (Opposite.op Y)), U₀.ι.app (Opposite.op Y) a = f.app (Opposite.op Y) b →
      (a ∈ T₀.obj (Opposite.op Y) ↔ b ∈ T₂.obj (Opposite.op Y)) := by
    intro Y a b hab
    have hbU : b ∈ (U₀.preimage f).obj (Opposite.op Y) := by
      change f.app _ b ∈ U₀.obj _
      rw [← hab]; exact a.2
    have key : b ∈ (T₀'.preimage f).obj (Opposite.op Y) ↔ b ∈ T₂.obj (Opposite.op Y) := by
      have hn : T₂ ⊓ U₀.preimage f = T₀'.preimage f := hT₂ none
      rw [← hn]
      exact ⟨fun hb => hb.1, fun hb => ⟨hb, hbU⟩⟩
    rw [← key]
    change a ∈ T₀.obj _ ↔ f.app _ b ∈ T₀'.obj _
    rw [← hab, ← hT₀'pre]
    rfl
  set T' := squareGlue B S hS U₀ f T₀ T₂ with hT'def
  have hT'c : IsClosedSubspace B S hS T' := isClosedSubspace_squareGlue hW h hT₀c hT₂c hcomp
  have hT'f : IsFinitePresentation B S hS T'.ι :=
    isFinitePresentation_squareGlue hW h hT₀c hT₂c hcomp hT₀f hT₂f
  have hT'U₀ : T' ⊓ U₀ = T₀' := by
    rw [← image_ι_preimage_ι, preimage_ι_squareGlue hW h hT₂c hcomp]
  have hT'f₂ : T'.preimage f = T₂ := preimage_squareGlue hW h hT₂c hcomp
  refine ⟨T', hT'c, hT'f, fun i => ?_⟩
  have hTa : IsAlgebraicSpace B S hS (T i).toFunctor :=
    isAlgebraicSpace_toFunctor_of_le (hTU i) (hTc i).1
  have hT'Ua : IsAlgebraicSpace B S hS (T' ⊓ U i).toFunctor := by
    refine isAlgebraicSpace_toFunctor_of_le (Ω := U i) inf_le_right ?_
    rw [preimage_inf_ι_eq]
    exact (isClosedSubspace_preimage B S hS (U i).ι T' hW (hUa i) hT'c).1
  have h₀ : (T' ⊓ U i) ⊓ U₀ = T i ⊓ U₀ := by rw [inf_right_comm, hT'U₀, hT₀'inf i]
  have h₂ : (T' ⊓ U i).preimage f = (T i).preimage f := by
    rw [preimage_inf_eq, hT'f₂]
    exact hT₂ (some i)
  exact le_antisymm
    (le_of_inf_eq_of_preimage_eq_of_isElementaryDistinguishedSquare hW h hTa.isSheaf h₀ h₂)
    (le_of_inf_eq_of_preimage_eq_of_isElementaryDistinguishedSquare hW h hT'Ua.isSheaf
      h₀.symm h₂.symm)

/-- **Finitely presented closed subspaces extend from quasi-compact opens of a quasi-compact
and quasi-separated algebraic space.** This is the induction principle of Stacks 08GP applied
to `AlgebraicGeometry.Space.ExtendsClosedSubspaces`: the affine case is
`AlgebraicGeometry.Space.exists_closedSubspace_extension_of_isAffineSpace` and the step across
an elementary distinguished square is
`AlgebraicGeometry.Space.ExtendsClosedSubspaces.of_isElementaryDistinguishedSquare`. -/
theorem extendsClosedSubspaces_of_isQuasiCompactSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ExtendsClosedSubspaces B S hS X.1 :=
  qcqs_induction_on_self B S hS hZ X hXqc hXqs (fun Y _ => ExtendsClosedSubspaces B S hS Y)
    (fun V hV => fun _ _ U hU hUqc T hTU hTc hTf hcompat =>
      exists_closedSubspace_extension_of_isAffineSpace B S hS V.1.left.property hV U hU hUqc T hTU
        hTc hTf hcompat)
    (fun W _ U f _ h _ hWqs hUqc hVa hPU _ _ =>
      ExtendsClosedSubspaces.of_isElementaryDistinguishedSquare hZ W.1.left.property hWqs U f h
        hUqc hVa hPU)

/-- **Extending a finitely presented closed subspace away from an open subspace.**  Let `X` be
a quasi-compact and quasi-separated algebraic space, let `U, V ⊆ X` be quasi-compact open
subspaces and let `W ⊆ V` be a closed subspace of finite presentation whose points avoid those of
`U ∩ V`.  Then there is a closed subspace `Z ⊆ X` of finite presentation whose points avoid
those of `U` and with `Z ∩ V = W`.

This is the closed-subspace form of the first two steps of the proof of Stacks 086D, which the
source obtains from Stacks 0853.  Here `W` on `V` and the empty closed subspace on `U` agree on
`U ∩ V`, because `W` has no points there, and
`AlgebraicGeometry.Space.extendsClosedSubspaces_of_isQuasiCompactSpace` extends the pair. -/
theorem exists_closedSubspace_extension_disjoint (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (U V : Subfunctor X.1) (hU : IsOpenSubspace B S hS U) (hV : IsOpenSubspace B S hS V)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (W : Subfunctor V.toFunctor) (hW : IsClosedSubspace B S hS W)
    (hWfp : IsFinitePresentation B S hS W.ι)
    (hWU : Disjoint (subspacePointSet B S hS V.toFunctor (U.preimage V.ι))
      (subspacePointSet B S hS V.toFunctor W)) :
    ∃ Z : Subfunctor X.1, IsClosedSubspace B S hS Z ∧ IsFinitePresentation B S hS Z.ι ∧
      Disjoint (subspacePointSet B S hS X.1 U) (subspacePointSet B S hS X.1 Z) ∧
        Z.preimage V.ι = W := by
  classical
  -- the empty closed subspace of `X`
  set E : Subfunctor X.1 := (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS)
    with hEdef
  have hEo : IsOpenSubspace B S hS E := isOpenSubspace_sheafify_bot B S hS X.1 X.2
  have hEc : IsClosedSubspace B S hS E := by
    rw [hEdef, ← openSubspaceOfPoints_empty B S hS X.1]
    exact isClosedSubspace_openSubspaceOfPoints B S hS X.2 ∅ isOpen_empty isClosed_empty
  have hEfp : IsFinitePresentation B S hS E.ι :=
    ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hEo.2,
      isQuasiCompact_of_isClosedImmersion' B S hS hEc.2,
      isQuasiSeparated_of_mono B S hS _ inferInstance⟩
  have hEpts : Set.range (pointsMap B S hS E.toFunctor E.ι) = ∅ :=
    range_pointsMap_ι_sheafify_bot B S hS X.1
  -- `W` meets `U` in the empty subspace
  have hWUE : W.image V.ι ⊓ U = E ⊓ U ⊓ V := by
    set EV : Subfunctor V.toFunctor :=
      (⊥ : Subfunctor V.toFunctor).sheafify (BigFppfOver.topology B S hS) with hEVdef
    have hEVE : EV ≤ E.preimage V.ι := fun T x hx => hx
    have hEVW : EV ≤ W := Subfunctor.sheafify_le (G := ⊥) (G' := W) bot_le
      ((isSheaf_iff_isSheaf_of_type _ _).1 hV.1.isSheaf)
      ((isSheaf_iff_isSheaf_of_type _ _).1 hW.1.isSheaf)
    refine le_antisymm (le_inf (le_inf ?_ inf_le_right) (inf_le_left.trans (image_ι_le V W)))
      (le_inf ?_ (inf_le_left.trans inf_le_right))
    · rw [← image_ι_inf_preimage_ι, Subfunctor.image_le_iff]
      refine le_trans ?_ hEVE
      refine le_of_range_pointsMap_ι_subset B S hS
        (isOpenSubspace_sheafify_bot B S hS V.toFunctor hV.1) ?_
      rintro p ⟨q, rfl⟩
      exfalso
      have hpt : ∀ A : Subfunctor V.toFunctor, W ⊓ U.preimage V.ι ≤ A →
          pointsMap B S hS _ (W ⊓ U.preimage V.ι).ι q ∈ subspacePointSet B S hS V.toFunctor A :=
        fun A hA => ⟨pointsMap B S hS _ (Subfunctor.homOfLe hA) q, by
          rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]⟩
      exact Set.disjoint_left.1 hWU (hpt _ inf_le_right) (hpt _ inf_le_left)
    · rintro T x ⟨⟨hxE, -⟩, hxV⟩
      exact ⟨⟨x, hxV⟩, hEVW T (show _ ∈ EV.obj T from hxE), rfl⟩
  -- the compatible pair on `V` and `U`
  let UU : Bool → Subfunctor X.1 := fun b => bif b then V else U
  let TT : Bool → Subfunctor X.1 := fun b => bif b then W.image V.ι else E ⊓ U
  obtain ⟨Z, hZc, hZfp, hZ⟩ := extendsClosedSubspaces_of_isQuasiCompactSpace hZ X hXqc
    hXqs Bool UU (fun b => by cases b <;> assumption) (fun b => by cases b <;> assumption) TT
    (fun b => by cases b
                 · exact inf_le_right
                 · exact image_ι_le V W)
    (fun b => by
      cases b
      · change IsClosedSubspace B S hS ((E ⊓ U).preimage U.ι)
        rw [preimage_inf_ι_eq]
        exact isClosedSubspace_preimage B S hS U.ι E X.2 hU.1 hEc
      · change IsClosedSubspace B S hS ((W.image V.ι).preimage V.ι)
        rw [preimage_ι_image_ι]
        exact hW)
    (fun b => by
      cases b
      · change IsFinitePresentation B S hS ((E ⊓ U).preimage U.ι).ι
        rw [preimage_inf_ι_eq]
        exact isFinitePresentation_of_isPullback B S hS
          (isClosedSubspace_preimage B S hS U.ι E X.2 hU.1 hEc).1 hEc.1 hU.1 X.2
          (Subfunctor.isPullback_preimage U.ι E) hEfp
      · change IsFinitePresentation B S hS ((W.image V.ι).preimage V.ι).ι
        rw [preimage_ι_image_ι]
        exact hWfp)
    (fun b b' => by
      cases b <;> cases b'
      · rfl
      · exact hWUE.symm
      · exact hWUE
      · rfl)
  refine ⟨Z, hZc, hZfp, Set.disjoint_left.2 ?_, ?_⟩
  · rintro p ⟨a, rfl⟩ ⟨c, hc⟩
    obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
      (Subfunctor.isPullback_preimage Z.ι U) a c hc.symm
    have hrange : Subfunctor.range ((U.preimage Z.ι).ι ≫ Z.ι) ≤ E := by
      rw [Subfunctor.range_comp, Subfunctor.range_ι, image_ι_preimage_ι, inf_comm]
      exact (hZ false).trans_le inf_le_left
    have : pointsMap B S hS U.toFunctor U.ι a ∈
        Set.range (pointsMap B S hS E.toFunctor E.ι) := by
      refine ⟨pointsMap B S hS _ (Subfunctor.lift _ hrange) w, ?_⟩
      rw [← pointsMap_comp_apply, Subfunctor.lift_ι, pointsMap_comp_apply, hw, ← hc]
    rw [hEpts] at this
    exact this
  · have h1 : Z ⊓ V = W.image V.ι := hZ true
    rw [← preimage_ι_image_ι V W, ← h1, preimage_inf_ι_eq]

end AlgebraicGeometry.Space

end
