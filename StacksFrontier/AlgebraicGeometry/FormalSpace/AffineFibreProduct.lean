module

public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Characterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Diagonal
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteCoproducts
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Fibre products of affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `X ⟶ Z` and `Y ⟶ Z` be morphisms of
fppf sheaves on the big fppf site of `S`. **Stacks 0AN3, clause (1)** says that if `Z` is
separated and `X` and `Y` are affine formal algebraic spaces, then so is the fibre product
`X ×_Z Y`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsSeparated`: separatedness of an fppf sheaf, in the form of
  clause (2) of **Stacks 0AJ6**, which is what **Stacks 0AJ7** names.
* `AlgebraicGeometry.FormalSpace.HasRepresentableRelativeProducts`: representability of the
  fibre product over an fppf sheaf of two sheaves represented by objects of the site.

## Main results

* `AlgebraicGeometry.FormalSpace.hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace`:
  an affine formal algebraic space has representable relative products.
* `satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts`: the
  set-theoretic condition of **Stacks 0AIS** is inherited by a fibre product of two sheaves
  satisfying it whose factors and base have representable relative products.
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_pullback`: the set-theoretic
  condition of **Stacks 0AIS** for a fibre product of affine formal algebraic spaces.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback`:
  **Stacks 0AN3, clause (1)**.

## Implementation notes

Separatedness is recorded in the reduction-free form of Stacks 0AJ6, clause (2), rather than as
separatedness of the reduction of a formal algebraic space, and it is stated for an arbitrary
fppf sheaf, so the results below need no formal algebraic space structure on the base. A fibre
product is specified by a cartesian square over the sheafified Yoneda embedding rather than by a
chosen object, so the condition does not presuppose that the site is subcanonical.

Representability of the fibre product over `Z` of two sheaves represented by objects of the site
is a separate hypothesis, `HasRepresentableRelativeProducts`. It is the representability clause
of Stacks 0AIP when `Z` is a formal algebraic space, it is the standing hypothesis on the base
in Stacks 0AJ2, and it is automatic when `Z` is an affine formal algebraic space. By
`CategoryTheory.Functor.relativelyRepresentable.diag_iff` it is equivalent to representability
of the diagonal of `Z`.

The name `IsSeparated` shadows `AlgebraicGeometry.IsSeparated`, which is a property of a
morphism of schemes; the two are distinguished by the enclosing namespace.

## References

* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AI8](https://stacks.math.columbia.edu/tag/0AI8)
* [Stacks Project, Tag 0AIB](https://stacks.math.columbia.edu/tag/0AIB)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

/-- If `a` and `b` have a property stable under base change and composition, so does the
composite `k₁ ≫ k₂` of the two base changes in the comparison morphism. -/
private theorem comp_mem_of_isPullback_comparison {C : Type*} [Category C] {P : MorphismProperty C}
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] {X Y A₁ A₂ Q V R : C}
    {a : A₁ ⟶ X} {b : A₂ ⟶ Y} {c₁ : V ⟶ Y} {c₂ : V ⟶ A₁} {k₁ : Q ⟶ V} {k₂ : V ⟶ R}
    {β : Q ⟶ A₂} {s : R ⟶ X}
    (sq₁ : IsPullback β k₁ b c₁) (sq₂ : IsPullback c₂ k₂ a s) (ha : P a) (hb : P b) :
    P (k₁ ≫ k₂) :=
  MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isPullback sq₁ hb)
    (MorphismProperty.of_isPullback sq₂ ha)

section Comparison

variable {C : Type*} [Category C] [HasPullbacks C]

/-- The comparison morphism from a fibre product of two morphisms `α`, `β` lying over
`a ≫ p` and `b ≫ q` into the fibre product of `p` and `q` factors as a base change of `b`
followed by a base change of `a`. -/
private theorem exists_pullback_comparison {X Y Z A₁ A₂ P : C} (p : X ⟶ Z) (q : Y ⟶ Z)
    (a : A₁ ⟶ X) (b : A₂ ⟶ Y) {α : P ⟶ A₁} {β : P ⟶ A₂}
    (sq : IsPullback α β (a ≫ p) (b ≫ q)) :
    ∃ (V : C) (c₁ : V ⟶ Y) (c₂ : V ⟶ A₁) (k₁ : P ⟶ V) (k₂ : V ⟶ pullback p q),
      IsPullback β k₁ b c₁ ∧ IsPullback c₂ k₂ a (pullback.fst p q) ∧
        (k₁ ≫ k₂) ≫ pullback.fst p q = α ≫ a ∧
        (k₁ ≫ k₂) ≫ pullback.snd p q = β ≫ b := by
  have tV : IsPullback (pullback.fst (a ≫ p) q) (pullback.snd (a ≫ p) q) (a ≫ p) q :=
    IsPullback.of_hasPullback (a ≫ p) q
  have t0 : IsPullback (pullback.fst p q) (pullback.snd p q) p q :=
    IsPullback.of_hasPullback p q
  let k₂ : pullback (a ≫ p) q ⟶ pullback p q :=
    pullback.lift (pullback.fst (a ≫ p) q ≫ a) (pullback.snd (a ≫ p) q)
      (by rw [Category.assoc]; exact pullback.condition)
  have hk₂fst : k₂ ≫ pullback.fst p q = pullback.fst (a ≫ p) q ≫ a :=
    pullback.lift_fst _ _ _
  have hk₂snd : k₂ ≫ pullback.snd p q = pullback.snd (a ≫ p) q :=
    pullback.lift_snd _ _ _
  let k₁ : P ⟶ pullback (a ≫ p) q :=
    pullback.lift α (β ≫ b) (by rw [Category.assoc]; exact sq.w)
  have hk₁fst : k₁ ≫ pullback.fst (a ≫ p) q = α := pullback.lift_fst _ _ _
  have hk₁snd : k₁ ≫ pullback.snd (a ≫ p) q = β ≫ b := pullback.lift_snd _ _ _
  refine ⟨pullback (a ≫ p) q, pullback.snd (a ≫ p) q, pullback.fst (a ≫ p) q, k₁, k₂,
    IsPullback.of_bot (by rw [hk₁fst]; exact sq.flip) hk₁snd.symm tV.flip,
    IsPullback.of_bot (by rw [hk₂snd]; exact tV) hk₂fst.symm t0, ?_, ?_⟩
  · rw [Category.assoc, hk₂fst, ← Category.assoc, hk₁fst]
  · rw [Category.assoc, hk₂snd, hk₁snd]

end Comparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An fppf sheaf `X` on the big fppf site of `S` is *separated* when, for every pair of morphisms
to `X` from sheaves represented by affine schemes over `S`, every object of the site representing
their fibre product is affine and the canonical map from the tensor product over `ℤ` of the two
coordinate rings to its coordinate ring is surjective.

The condition quantifies over the objects of the site representing the fibre product, so on an
fppf sheaf whose fibre products are not representable it holds vacuously. On a formal algebraic
space it agrees with `AlgebraicGeometry.FormalSpace.IsSeparatedFormalAlgebraicSpace`, by
`AlgebraicGeometry.FormalSpace.isSeparatedFormalAlgebraicSpace_iff_isSeparated`. -/
@[stacks 0AJ7 "clause (2): separated, in the form of clause (2) of Stacks 0AJ6"]
abbrev IsSeparated (X : FppfSheaf B S hS) : Prop :=
  ∀ (U V P : BigFppfOver B S hS)
      (f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X)
      (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X)
      (p : P ⟶ U) (q : P ⟶ V),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
    IsPullback ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f g →
    IsAffine ((BigFppfOver.toScheme B S hS).obj P) ∧
      Function.Surjective
        (Algebra.TensorProduct.lift
          (((BigFppfOver.toScheme B S hS).map p).appTop.hom.toIntAlgHom)
          (((BigFppfOver.toScheme B S hS).map q).appTop.hom.toIntAlgHom)
          (fun _ _ ↦ Commute.all _ _))

/-- An fppf sheaf `X` on the big fppf site of `S` *has representable relative products* when
every morphism to `X` from a sheaf represented by an object of the site is relatively
representable, so that the fibre product over `X` of two such sheaves is again represented by
an object of the site. -/
abbrev HasRepresentableRelativeProducts (X : FppfSheaf B S hS) : Prop :=
  ∀ ⦃a : BigFppfOver B S hS⦄
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj a ⟶ X),
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable g

/-- A composition of thickenings of schemes is a thickening. -/
instance : MorphismProperty.IsStableUnderComposition
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) where
  comp_mem f g hf hg := by
    obtain ⟨_, hf₂⟩ := hf
    obtain ⟨_, hg₂⟩ := hg
    exact ⟨inferInstance, by simpa using hg₂.comp hf₂⟩

/-- A base change of an epimorphism of fppf sheaves along a cartesian square is an epimorphism. -/
private theorem epi_of_isPullback {P X Y Z : FppfSheaf B S hS} {f' : P ⟶ X} {g' : P ⟶ Y}
    {g : X ⟶ Z} {f : Y ⟶ Z} (sq : IsPullback f' g' g f) (hg : Epi g) : Epi g' := by
  have : Epi (pullback.snd g f) := Sheaf.epi_pullback_snd g f hg
  rw [← sq.isoPullback_hom_snd]
  infer_instance

/-- Every morphism to an affine formal algebraic space from a sheaf represented by an object of
the site is relatively representable. -/
theorem hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    HasRepresentableRelativeProducts B S hS X := by
  obtain ⟨-, I, pre, hI, hdir, D, hD, ⟨e⟩⟩ := hX
  let : Preorder I := pre
  let : Nonempty I := hI
  let : IsDirected I (· ≤ ·) := hdir
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Full :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).full
  have : PreservesLimitsOfShape (Discrete WalkingPair)
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) :=
    preservesLimitsOfShape_of_natIso
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)).symm
  intro a g
  exact Functor.relativelyRepresentable.of_diag
    (diagonal_isClosedImmersion B S hS D hD X e.symm).rep g

/-- **The set-theoretic condition of Stacks 0AIS is inherited by a fibre product.** If the two
factors `X` and `Y` satisfy the condition and `X`, `Y` and the base `Z` have representable
relative products, then `X ×_Z Y` satisfies it. -/
theorem satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZrep : HasRepresentableRelativeProducts B S hS Z)
    (hXrep : HasRepresentableRelativeProducts B S hS X)
    (hYrep : HasRepresentableRelativeProducts B S hS Y)
    (hXset : SatisfiesSetTheoreticCondition B S hS X)
    (hYset : SatisfiesSetTheoreticCondition B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS (pullback p q) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let G := sheafToPresheaf J (Type (u + 1))
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  have : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  obtain ⟨UX, -, hUX, -, hUXrep, -, fX, hfX, -⟩ := hXset
  obtain ⟨UY, -, hUY, -, hUYrep, -, fY, hfY, -⟩ := hYset
  let eUX : hUX ≅ F.obj UX := (Functor.FullyFaithful.ofFullyFaithful G).preimageIso
    (Classical.choice hUXrep ≪≫ (G.mapIso (eG.app UX)).symm)
  let eUY : hUY ≅ F.obj UY := (Functor.FullyFaithful.ofFullyFaithful G).preimageIso
    (Classical.choice hUYrep ≪≫ (G.mapIso (eG.app UY)).symm)
  let fX' : F.obj UX ⟶ X := eUX.inv ≫ fX
  let fY' : F.obj UY ⟶ Y := eUY.inv ≫ fY
  have hfX' : Epi fX' := by dsimp only [fX']; infer_instance
  have hfY' : Epi fY' := by dsimp only [fY']; infer_instance
  have hrep : F.relativelyRepresentable (fX' ≫ p) := hZrep (fX' ≫ p)
  obtain ⟨V, c₁, c₂, k₁, k₂, sq₁, sq₂, -, -⟩ :=
    exists_pullback_comparison p q fX' fY' (hrep.isPullback' (fY' ≫ q))
  have hk₁ : Epi k₁ := epi_of_isPullback B S hS sq₁ hfY'
  have hk₂ : Epi k₂ := epi_of_isPullback B S hS sq₂ hfX'
  have hmrep : F.relativelyRepresentable (k₁ ≫ k₂) :=
    comp_mem_of_isPullback_comparison sq₁ sq₂ (hXrep fX') (hYrep fY')
  obtain ⟨R, sndR, fstR, sqR⟩ := hmrep (k₁ ≫ k₂)
  exact ⟨hrep.pullback (fY' ≫ q), R, F.obj (hrep.pullback (fY' ≫ q)), F.obj R,
    ⟨G.mapIso (eG.app (hrep.pullback (fY' ≫ q)))⟩, ⟨G.mapIso (eG.app R)⟩,
    k₁ ≫ k₂, inferInstance, sqR.isoPullback.hom, inferInstance⟩

/-- The set-theoretic condition of **Stacks 0AIS** holds for the fibre product of two affine
formal algebraic spaces over an fppf sheaf with representable relative products. -/
theorem satisfiesSetTheoreticCondition_pullback
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZrep : HasRepresentableRelativeProducts B S hS Z)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS (pullback p q) :=
  satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts B S hS p q hZrep
    (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hX)
    (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hY) hX.1 hY.1

/-- The fibre product of two affine formal algebraic spaces over a separated fppf sheaf with
representable relative products is an affine formal algebraic space. -/
@[stacks 0AN3 "the fibre product of affine formal algebraic spaces over a separated base"]
theorem isAffineFormalAlgebraicSpace_pullback
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZrep : HasRepresentableRelativeProducts B S hS Z)
    (hZsep : IsSeparated B S hS Z)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) :
    IsAffineFormalAlgebraicSpace B S hS (pullback p q) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let K := BigAffineFppf.inclusion B S hS
  let Q : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  have : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  have : Q.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
  have := MorphismProperty.relative_isStableUnderBaseChange (P := Q) (F := F)
  refine (isAffineFormalAlgebraicSpace_iff B S hS _).mpr
    ⟨?_, satisfiesSetTheoreticCondition_pullback B S hS p q hZrep hX hY⟩
  intro U f
  obtain ⟨T₁, g₁, h₁, hr₁, ht₁, he₁⟩ :=
    ((isAffineFormalAlgebraicSpace_iff B S hS X).mp hX).1 U (f ≫ pullback.fst p q)
  obtain ⟨T₂, g₂, h₂, hr₂, ht₂, he₂⟩ :=
    ((isAffineFormalAlgebraicSpace_iff B S hS Y).mp hY).1 U (f ≫ pullback.snd p q)
  have hrep : F.relativelyRepresentable (h₁ ≫ p) := hZrep (h₁ ≫ p)
  have hsq := hrep.isPullback' (h₂ ≫ q)
  obtain ⟨hPaff, -⟩ := hZsep (K.obj T₁) (K.obj T₂) (hrep.pullback (h₂ ≫ q))
    (h₁ ≫ p) (h₂ ≫ q) (hrep.fst' (h₂ ≫ q)) (hrep.snd (h₂ ≫ q))
    T₁.property T₂.property hsq
  obtain ⟨V, c₁, c₂, k₁, k₂, sq₁, sq₂, hmfst, hmsnd⟩ :=
    exists_pullback_comparison p q h₁ h₂ hsq
  have hi : F.map (F.preimage g₁) ≫ (h₁ ≫ p) = F.map (F.preimage g₂) ≫ (h₂ ≫ q) := by
    rw [F.map_preimage, F.map_preimage, ← Category.assoc, ← Category.assoc, he₁, he₂,
      Category.assoc, Category.assoc, pullback.condition]
  let w : K.obj U ⟶ hrep.pullback (h₂ ≫ q) :=
    hrep.lift' (F.preimage g₁) (F.preimage g₂) hi
  have hwfst : F.map w ≫ F.map (hrep.fst' (h₂ ≫ q)) = g₁ := by
    rw [← Functor.map_comp, hrep.lift'_fst, F.map_preimage]
  have hwsnd : F.map w ≫ F.map (hrep.snd (h₂ ≫ q)) = g₂ := by
    rw [← Functor.map_comp, hrep.lift'_snd, F.map_preimage]
  refine ⟨⟨hrep.pullback (h₂ ≫ q), hPaff⟩, F.map w, k₁ ≫ k₂, ?_, ?_, ?_⟩
  · exact comp_mem_of_isPullback_comparison sq₁ sq₂ hr₁ hr₂
  · exact comp_mem_of_isPullback_comparison sq₁ sq₂ ht₁ ht₂
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hmfst, ← Category.assoc, hwfst, he₁]
    · rw [Category.assoc, hmsnd, ← Category.assoc, hwsnd, he₂]

end AlgebraicGeometry.FormalSpace

end
