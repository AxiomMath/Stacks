module

public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.RestrictionCoverShortExact
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.UnboundedTriangle
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeCriteria
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# The Mayer–Vietoris triangle of a bounded below complex of injective sheaves of modules

Let `X` be a topological space with a sheaf of rings `O`, let `U` and `V` be opens with
`U ⊔ V = ⊤`, and let `I` be a bounded below complex of injective `O`-modules. Applying the
Mayer–Vietoris short exact sequence of [Stacks, Tag 01EB]

`0 ⟶ M ⟶ M|ᵁ ⊞ M|ⱽ ⟶ M|ᵁ⊓ⱽ ⟶ 0`,

where `M|ᵂ` denotes restriction to `W` followed by pushforward back to `X`, degreewise to `I`
gives a short exact sequence of complexes, split in each degree because `Iⁿ` is injective. It is
therefore a distinguished triangle of `D⁺(O)`

`I ⟶ I|ᵁ ⊞ I|ⱽ ⟶ I|ᵁ⊓ⱽ ⟶ I⟦1⟧`.

The consequence recorded here: a natural transformation of triangulated functors out of `D⁺(O)`,
compatible with the shift, is invertible at `I` as soon as it is invertible at `I|ᵁ`, `I|ⱽ` and
`I|ᵁ⊓ⱽ`.

## Main results

* `Stacks.Cohomology.RestrictionCover.exists_plus_triangle`: a distinguished triangle of `D(C)`
  whose vertices are bounded below is the image of a distinguished triangle of `D⁺(C)`.
* `Stacks.Cohomology.RestrictionCover.isIso_app_of_restrictionCover`: the two out of three
  statement above.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

universe u

namespace Stacks.Cohomology.RestrictionCover

/-! ### Lifting a triangle with bounded below vertices -/

/-- Composing with the image of an identity does nothing. -/
theorem comp_map_id_eq {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟) {A : 𝒟} {B : 𝒞}
    {x y : A ⟶ Φ.obj B} (h : x = y) : x ≫ Φ.map (𝟙 B) = y := by
  rw [h, Φ.map_id, Category.comp_id]

section Lift

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **A distinguished triangle of `D(C)` with bounded below vertices lifts to `D⁺(C)`.** The
lifted triangle has the same vertices and, through the inclusion `D⁺(C) ⥤ D(C)`, the same
morphisms. -/
theorem exists_plus_triangle (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (h₁ : DerivedCategory.TStructure.t.plus T.obj₁) (h₂ : DerivedCategory.TStructure.t.plus T.obj₂)
    (h₃ : DerivedCategory.TStructure.t.plus T.obj₃) :
    ∃ T' : Triangle (DerivedCategory.Plus C), T' ∈ distTriang _ ∧
      T'.obj₁ = ⟨T.obj₁, h₁⟩ ∧ T'.obj₂ = ⟨T.obj₂, h₂⟩ ∧ T'.obj₃ = ⟨T.obj₃, h₃⟩ := by
  let X₁ : DerivedCategory.Plus C := ⟨T.obj₁, h₁⟩
  let X₂ : DerivedCategory.Plus C := ⟨T.obj₂, h₂⟩
  let X₃ : DerivedCategory.Plus C := ⟨T.obj₃, h₃⟩
  let a : X₁ ⟶ X₂ := DerivedCategory.Plus.ι.preimage T.mor₁
  let b : X₂ ⟶ X₃ := DerivedCategory.Plus.ι.preimage T.mor₂
  let c : X₃ ⟶ X₁⟦(1 : ℤ)⟧ := DerivedCategory.Plus.ι.preimage
    (T.mor₃ ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app X₁)
  refine ⟨Triangle.mk a b c, ?_, rfl, rfl, rfl⟩
  show DerivedCategory.Plus.ι.mapTriangle.obj (Triangle.mk a b c) ∈ distTriang _
  refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_)
  · exact (Category.comp_id _).trans
      ((DerivedCategory.Plus.ι.map_preimage (X := X₁) (Y := X₂) T.mor₁).trans
        (Category.id_comp _).symm)
  · exact (Category.comp_id _).trans
      ((DerivedCategory.Plus.ι.map_preimage (X := X₂) (Y := X₃) T.mor₂).trans
        (Category.id_comp _).symm)
  · have h : DerivedCategory.Plus.ι.map c ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app X₁ = T.mor₃ := by
      rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app]
      exact Category.comp_id _
    exact (comp_map_id_eq _ h).trans (Category.id_comp _).symm

/-- **A degreewise split short exact sequence of bounded below complexes is a distinguished
triangle of `D⁺(C)`.** -/
theorem exists_plus_triangle_of_degreewiseSplit (S : ShortComplex (CochainComplex C ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)
    (h₁ : CochainComplex.plus C S.X₁) (h₂ : CochainComplex.plus C S.X₂)
    (h₃ : CochainComplex.plus C S.X₃) :
    ∃ T' : Triangle (DerivedCategory.Plus C), T' ∈ distTriang _ ∧
      T'.obj₁ = DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj ⟨S.X₁, h₁⟩) ∧
      T'.obj₂ = DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj ⟨S.X₂, h₂⟩) ∧
      T'.obj₃ = DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj ⟨S.X₃, h₃⟩) :=
  exists_plus_triangle
    (DerivedCategory.Qh.mapTriangle.obj (CochainComplex.trianglehOfDegreewiseSplit S σ))
    (DerivedCategory.Qh.map_distinguished _
      (CochainComplex.trianglehOfDegreewiseSplit_distinguished S σ))
    (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj ⟨S.X₁, h₁⟩)).property
    (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj ⟨S.X₂, h₂⟩)).property
    (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj ⟨S.X₃, h₃⟩)).property

end Lift

/-! ### Transport along isomorphisms and biproducts -/

section Transport

variable {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] {Φ Ψ : 𝒞 ⥤ 𝒟} (τ : Φ ⟶ Ψ)

/-- A natural transformation invertible at an object is invertible at every isomorphic
object. -/
theorem isIso_app_of_iso {X Y : 𝒞} (e : X ≅ Y) (h : IsIso (τ.app Y)) : IsIso (τ.app X) := by
  have hX : τ.app X = Φ.map e.hom ≫ τ.app Y ≫ Ψ.map e.inv := by
    have hn := τ.naturality e.hom
    rw [← Category.assoc, hn, Category.assoc, ← Ψ.map_comp, e.hom_inv_id, Ψ.map_id,
      Category.comp_id]
  rw [hX]
  infer_instance

/-- A natural transformation of additive functors is invertible at the point of a binary bicone
with `fst ≫ inl + snd ≫ inr = 𝟙` as soon as it is invertible at the two summands. -/
theorem isIso_app_of_bicone [Preadditive 𝒞] [Preadditive 𝒟] [Φ.Additive] [Ψ.Additive]
    {P Q : 𝒞} (b : BinaryBicone P Q) (hb : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt)
    (hP : IsIso (τ.app P)) (hQ : IsIso (τ.app Q)) : IsIso (τ.app b.pt) := by
  refine ⟨Ψ.map b.fst ≫ inv (τ.app P) ≫ Φ.map b.inl + Ψ.map b.snd ≫ inv (τ.app Q) ≫ Φ.map b.inr,
    ?_, ?_⟩
  · rw [Preadditive.comp_add, ← Category.assoc, ← τ.naturality, Category.assoc,
      IsIso.hom_inv_id_assoc, ← Category.assoc (τ.app b.pt), ← τ.naturality, Category.assoc,
      IsIso.hom_inv_id_assoc, ← Φ.map_comp, ← Φ.map_comp, ← Φ.map_add, hb, Φ.map_id]
  · rw [Preadditive.add_comp, Category.assoc, Category.assoc, τ.naturality, IsIso.inv_hom_id_assoc,
      Category.assoc, Category.assoc, τ.naturality, IsIso.inv_hom_id_assoc, ← Ψ.map_comp,
      ← Ψ.map_comp, ← Ψ.map_add, hb, Ψ.map_id]

end Transport

/-! ### The Mayer–Vietoris triangle -/

section Cover

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Sheaves of modules over `O` form an abelian category; recorded once so that the instance
searches for the triangulated structure of `D⁺(O)` find it directly. -/
@[instance_reducible] local instance abelianSheafOfModules : Abelian (SheafOfModules.{u} O) :=
  inferInstance

/-- The Mayer–Vietoris short complex of a cochain complex of injectives is split in each
degree: its first term is injective. -/
def restrictionCoverSplitting (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) [∀ n, Injective (K.X n)] (n : ℤ) :
    ((restrictionCoverShortComplex O U V K).map
      (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).Splitting :=
  have hS := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (restrictionCoverShortExact O U V hUV K) n
  have : Injective ((restrictionCoverShortComplex O U V K).map
      (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).X₁ :=
    inferInstanceAs (Injective (K.X n))
  have := hS.mono_f
  ShortComplex.Splitting.ofExactOfRetraction _ hS.exact
    (Injective.factorThru (𝟙 _) _) (Injective.comp_factorThru _ _) hS.epi_g

/-- The localization of a bounded below complex, as an object of `D⁺(O)`. -/
abbrev plusQ (K : CochainComplex.Plus (SheafOfModules.{u} O)) :
    DerivedCategory.Plus (SheafOfModules.{u} O) :=
  DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj K)

/-- The middle term of the Mayer–Vietoris short complex of a bounded below complex is the point
of a binary bicone on its two summands, whose two composites add up to the identity. -/
def middleBicone (U V : Opens X) (K : CochainComplex.Plus (SheafOfModules.{u} O)) :
    BinaryBicone ((restrictPush O U).mapCochainComplexPlus.obj K)
      ((restrictPush O V).mapCochainComplexPlus.obj K) where
  pt := (restrictionCoverMiddle O U V).mapCochainComplexPlus.obj K
  fst := ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex (restrictionCoverFst O U V) (ComplexShape.up ℤ)).app K.obj)
  snd := ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex (restrictionCoverSnd O U V) (ComplexShape.up ℤ)).app K.obj)
  inl := ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex (restrictionCoverInl O U V) (ComplexShape.up ℤ)).app K.obj)
  inr := ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex (restrictionCoverInr O U V) (ComplexShape.up ℤ)).app K.obj)
  inl_fst := by
    ext n : 2
    exact biprod.inl_fst
  inl_snd := by
    ext n : 2
    exact biprod.inl_snd
  inr_fst := by
    ext n : 2
    exact biprod.inr_fst
  inr_snd := by
    ext n : 2
    exact biprod.inr_snd

/-- The two composites of the bicone `middleBicone O U V K` add up to the identity. -/
theorem middleBicone_total (U V : Opens X) (K : CochainComplex.Plus (SheafOfModules.{u} O)) :
    (middleBicone O U V K).fst ≫ (middleBicone O U V K).inl +
      (middleBicone O U V K).snd ≫ (middleBicone O U V K).inr = 𝟙 _ := by
  ext n : 2
  exact biprod.total

/-- **The Mayer–Vietoris two out of three.** Let `τ : Φ ⟶ Ψ` be a natural transformation of
triangulated functors out of `D⁺(O)`, compatible with the shift, and let `K` be a bounded below
complex of injective `O`-modules. If `τ` is invertible at the restrictions of `K` to `U`, to `V`
and to `U ⊓ V`, pushed forward back to `X`, then `τ` is invertible at `K`. -/
theorem isIso_app_of_restrictionCover {𝒟 : Type*} [Category* 𝒟] [HasShift 𝒟 ℤ]
    [HasZeroObject 𝒟] [Preadditive 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
    {Φ Ψ : DerivedCategory.Plus (SheafOfModules.{u} O) ⥤ 𝒟} [Φ.CommShift ℤ] [Ψ.CommShift ℤ]
    [Φ.IsTriangulated] [Ψ.IsTriangulated] (τ : Φ ⟶ Ψ) [NatTrans.CommShift τ ℤ]
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (K : CochainComplex.Plus (SheafOfModules.{u} O))
    (hK : ∀ n, Injective (K.obj.X n))
    (hU : IsIso (τ.app (plusQ O ((restrictPush O U).mapCochainComplexPlus.obj K))))
    (hV : IsIso (τ.app (plusQ O ((restrictPush O V).mapCochainComplexPlus.obj K))))
    (hW : IsIso (τ.app (plusQ O ((restrictPush O (U ⊓ V)).mapCochainComplexPlus.obj K)))) :
    IsIso (τ.app (plusQ O K)) := by
  have : ∀ n, Injective (K.obj.X n) := hK
  let S := restrictionCoverShortComplex O U V K.obj
  obtain ⟨T, hT, h₁, h₂, h₃⟩ := exists_plus_triangle_of_degreewiseSplit S
    (restrictionCoverSplitting O U V hUV K.obj) K.property
    ((restrictionCoverMiddle O U V).mapCochainComplexPlus.obj K).property
    ((restrictPush O (U ⊓ V)).mapCochainComplexPlus.obj K).property
  have e₁ : T.obj₁ = plusQ O K := h₁
  refine e₁ ▸ Stacks.Cohomology.BaseChange.isIso_app_obj₁_of_triangle τ T hT ?_ ?_
  · rw [h₂]
    let Ξ : CochainComplex.Plus (SheafOfModules.{u} O) ⥤
        DerivedCategory.Plus (SheafOfModules.{u} O) :=
      HomotopyCategory.Plus.quotient _ ⋙ DerivedCategory.Plus.Qh
    have : (HomotopyCategory.Plus.quotient (SheafOfModules.{u} O)).Additive := by
      dsimp only [HomotopyCategory.Plus.quotient]
      infer_instance
    have : Ξ.Additive := Functor.instAdditiveComp _ _
    have hΞ : (Ξ.mapBinaryBicone (middleBicone O U V K)).fst ≫
        (Ξ.mapBinaryBicone (middleBicone O U V K)).inl +
        (Ξ.mapBinaryBicone (middleBicone O U V K)).snd ≫
        (Ξ.mapBinaryBicone (middleBicone O U V K)).inr = 𝟙 _ := by
      have h := congrArg Ξ.map (middleBicone_total O U V K)
      rwa [Ξ.map_add, Ξ.map_comp, Ξ.map_comp, Ξ.map_id] at h
    exact isIso_app_of_bicone τ _ hΞ hU hV
  · rwa [h₃]

end Cover

end Stacks.Cohomology.RestrictionCover

end
