module

public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismDescent

/-!
# Universal homeomorphisms descend along a jointly surjective flat family

The family form of Stacks 0DTQ, used in the proof of the Keel–Mori theorem (Stacks 0DUT): a
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is a universal homeomorphism as soon as its
base changes along a family of flat, locally finitely presented 1-morphisms `gⱼ : 𝒲ⱼ ⟶ 𝒴`, jointly
surjective on points, are. The proof is that of
`AlgebraicGeometry.Stack.universalHomeomorphism_of_fppfCover`, the single cover replaced by the
family; injectivity is read off the pieces directly.

## Main results

* `AlgebraicGeometry.Stack.universalHomeomorphism_of_flatFamily`
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Openness descends along a jointly surjective family of open maps through fibre squares.** -/
theorem isOpenMap_of_openSurjectiveFamily {J : Type*} {A Z : Type*} [TopologicalSpace A]
    [TopologicalSpace Z] {C D : J → Type*} [∀ j, TopologicalSpace (C j)]
    [∀ j, TopologicalSpace (D j)]
    (φ : A → Z) (p : ∀ j, C j → Z) (i : ∀ j, D j → A) (q : ∀ j, D j → C j)
    (hcomm : ∀ j d, φ (i j d) = p j (q j d))
    (hlift : ∀ j a c, φ a = p j c → ∃ d, i j d = a ∧ q j d = c)
    (hp : ∀ z, ∃ j c, p j c = z) (hpopen : ∀ j, IsOpenMap (p j))
    (hi : ∀ j, Continuous (i j)) (hqopen : ∀ j, IsOpenMap (q j)) :
    IsOpenMap φ := by
  intro U hU
  have key : φ '' U = ⋃ j, p j '' (q j '' (i j ⁻¹' U)) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨j, c, hc⟩ := hp (φ a)
      obtain ⟨d, hd₁, hd₂⟩ := hlift j a c hc.symm
      exact Set.mem_iUnion.2 ⟨j, q j d, ⟨d, by rwa [Set.mem_preimage, hd₁], rfl⟩,
        by rw [hd₂, hc]⟩
    · intro hz
      obtain ⟨j, _, ⟨d, hd, rfl⟩, rfl⟩ := Set.mem_iUnion.1 hz
      exact ⟨i j d, hd, hcomm j d⟩
  rw [key]
  exact isOpen_iUnion fun j => hpopen j _ (hqopen j _ (hU.preimage (hi j)))

/-- **Stacks 0DTQ for a jointly surjective family.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic
stacks over `S` and `gⱼ : 𝒲ⱼ ⟶ 𝒴` flat, locally finitely presented 1-morphisms, jointly surjective
on points. If for each `j` some 2-fibre product square of `(gⱼ, f)` has first projection
`𝒲ⱼ ×_𝒴 𝒳 ⟶ 𝒲ⱼ` a universal homeomorphism, then `f` is a universal homeomorphism. -/
theorem universalHomeomorphism_of_flatFamily {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {J : Type*} (𝒲 : J → AlgebraicStacks.{u, w} B S hS) (g : ∀ j, 𝒲 j ⟶ 𝒴)
    (hgSurj : ∀ y : AlgebraicStacks.points B S hS 𝒴,
      ∃ j, ∃ w : AlgebraicStacks.points B S hS (𝒲 j), AlgebraicStacks.pointsMap B S hS (g j) w = y)
    (hgFlat : ∀ j, AlgebraicStacks.IsFlat B S hS (g j))
    (hgLfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (g j))
    (K : ∀ j, Bicategory.TwoCommSq (g j) f) (hK : ∀ j, Bicategory.IsTwoFibreProduct (K j))
    (hgf : ∀ j, UniversalHomeomorphism B S hS (K j).fst) :
    UniversalHomeomorphism B S hS f := by
  classical
  intro 𝒵 k Q hQ
  let C := fun j => AlgebraicStacks.twoFibreProductSquare B S hS k (g j)
  have hC := fun j => AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS k (g j)
  let D := fun j => AlgebraicStacks.twoFibreProductSquare B S hS (C j).snd (K j).fst
  have hD := fun j =>
    AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (C j).snd (K j).fst
  let E := fun j => AlgebraicStacks.twoFibreProductSquare B S hS (C j).fst Q.fst
  have hE := fun j => AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (C j).fst Q.fst
  let _ := pointTopology B S hS 𝒵.val
  let _ := pointTopology B S hS Q.pt.val
  let _ := fun j => pointTopology B S hS (C j).pt.val
  let _ := fun j => pointTopology B S hS (E j).pt.val
  -- the base changes of the family are open and jointly surjective on points
  have hCsurj : ∀ z, ∃ j c, AlgebraicStacks.pointsMap B S hS (C j).fst c = z := by
    intro z
    obtain ⟨j, y, hy⟩ := hgSurj (AlgebraicStacks.pointsMap B S hS k z)
    obtain ⟨c, hc, -⟩ :=
      AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS (C j) (hC j) z y hy.symm
    exact ⟨j, c, hc⟩
  have hCopen : ∀ j, IsOpenMap (AlgebraicStacks.pointsMap B S hS (C j).fst) := fun j =>
    AlgebraicStacks.isOpenMap_pointsMap B S hS (C j).fst
      (AlgebraicStacks.isFlat_baseChange B S hS (g j) k (C j) (hC j) (hgFlat j))
      (AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS (g j) k (C j) (hC j)
        (hgLfp j))
  -- over each piece, the base change of `Q.fst` is a homeomorphism on points
  have hEfst : ∀ j, @IsHomeomorph _ _ (pointTopology B S hS (E j).pt.val)
      (pointTopology B S hS (C j).pt.val) (AlgebraicStacks.pointsMap B S hS (E j).fst) := by
    intro j
    -- stated at the reindexed pasted square, whose apex and first projection are those of `E j`
    have hEpaste := isHomeomorph_pointsMap_fst_of_isTwoFibreProduct B S hS
      (Bicategory.isTwoFibreProduct_reindexFst (C j).iso
        (Bicategory.isTwoFibreProduct_pasteFst Q hQ (E j) (hE j)))
      (Bicategory.isTwoFibreProduct_pasteFst (K j) (hK j) (D j) (hD j))
      (hgf j (C j).pt (C j).snd (D j) (hD j))
    exact hEpaste
  have hcomm : ∀ j e, AlgebraicStacks.pointsMap B S hS Q.fst
      (AlgebraicStacks.pointsMap B S hS (E j).snd e) =
      AlgebraicStacks.pointsMap B S hS (C j).fst
        (AlgebraicStacks.pointsMap B S hS (E j).fst e) := by
    intro j e
    have h := AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS (E j).iso.hom
    rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_comp] at h
    exact (congrFun h e).symm
  have hlift : ∀ j a c, AlgebraicStacks.pointsMap B S hS Q.fst a =
      AlgebraicStacks.pointsMap B S hS (C j).fst c →
      ∃ e, AlgebraicStacks.pointsMap B S hS (E j).snd e = a ∧
        AlgebraicStacks.pointsMap B S hS (E j).fst e = c := by
    intro j a c h
    obtain ⟨e, he₁, he₂⟩ :=
      AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS (E j) (hE j) c a h.symm
    exact ⟨e, he₂, he₁⟩
  refine ⟨continuous_pointsMap B S hS Q.pt.val 𝒵.val Q.fst.hom.hom, ?_, ?_, ?_⟩
  · exact isOpenMap_of_openSurjectiveFamily (AlgebraicStacks.pointsMap B S hS Q.fst)
      (fun j => AlgebraicStacks.pointsMap B S hS (C j).fst)
      (fun j => AlgebraicStacks.pointsMap B S hS (E j).snd)
      (fun j => AlgebraicStacks.pointsMap B S hS (E j).fst) hcomm hlift hCsurj hCopen
      (fun j => continuous_pointsMap B S hS (E j).pt.val Q.pt.val (E j).snd.hom.hom)
      (fun j => (hEfst j).isOpenMap)
  · intro a₁ a₂ h
    obtain ⟨j, c, hc⟩ := hCsurj (AlgebraicStacks.pointsMap B S hS Q.fst a₁)
    obtain ⟨e₁, he₁, he₁'⟩ := hlift j a₁ c hc.symm
    obtain ⟨e₂, he₂, he₂'⟩ := hlift j a₂ c (h ▸ hc.symm)
    have : e₁ = e₂ := (hEfst j).injective (he₁'.trans he₂'.symm)
    rw [← he₁, ← he₂, this]
  · intro z
    obtain ⟨j, c, hc⟩ := hCsurj z
    obtain ⟨e, he⟩ := (hEfst j).surjective c
    exact ⟨AlgebraicStacks.pointsMap B S hS (E j).snd e, by rwa [hcomm j e, he]⟩

end AlgebraicGeometry.Stack

end
