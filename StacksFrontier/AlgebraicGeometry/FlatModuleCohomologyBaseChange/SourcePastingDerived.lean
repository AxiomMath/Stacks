module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting

/-!
# Pasting the derived base change comparison along the fibre

Let two commutative squares of additive functors be stacked so that the *vertical* functors
compose:

```
A₀ --G''--> C₀
|E          |E'
v           v
A  --G'-->  C
|F          |F'
v           v
B  --G -->  D
```

A comparison of the lower square is a transformation `τ : F ⋙ G ⟶ G' ⋙ F'`, and one of the
upper square is `τ' : E ⋙ G' ⟶ G'' ⋙ E'`.  The outer rectangle has vertical composites
`E ⋙ F` and `E' ⋙ F'`, and a comparison of it is a transformation `R₀ ⋙ G ⟶ G₀ ⋙ R₁` for
functors `R₀`, `R₁`, `G₀` identified with `E ⋙ F`, `E' ⋙ F'` and `G''` by isomorphisms.  This
file proves that the descents of the three comparisons to bounded below derived categories
determine one another at the image of a bounded below complex of injective objects, in the form
needed to transfer invertibility: the lower square's descent is invertible at `Qh(E K)` as soon
as the rectangle's and the upper square's descents are invertible at `Qh K`.

Pasting along the base, where the two squares share a vertical functor and the *horizontal*
functors compose, is `Stacks.Cohomology.BaseChange.derived_paste`; this is the other direction,
and it is a different statement because `Stacks.Cohomology.BaseChange.derived` descends along
the derived functor of the vertical functor while the horizontal ones are assumed exact.

## The route

`Stacks.Cohomology.BaseChange.derived_fac_app` reads a descent at a bounded below complex `K`
as a factorization of `Stacks.Cohomology.BaseChange.onHomotopy` through the derived-functor
unit of the vertical functor, and that unit is invertible when `K` has injective terms.  So the
whole statement reduces to an identity between the three `onHomotopy`s, which is proved from

* the degreewise pasting identity `mapPlus_pasteSource_app`, the hypothesis evaluated at each
  term of `K`;
* naturality of the comparison `e` for the base functor, of the derived-functor unit of `RF'`,
  and of the two comparisons of right derived functors;
* `CategoryTheory.Functor.rightDerivedFunctorPlusComp_fac_app`, which contracts the iterated
  unit of `RE'` and `RF'` into the unit of `R(E' ⋙ F')`; and
* the hypothesis that the comparison `e` for the middle horizontal functor is its
  derived-functor unit, so that one unit cancels against one `e.inv`.

## Main definitions

* `Stacks.Cohomology.BaseChange.pasteSourceTargetIso`: the comparison
  `RF'(RE'(RG''(M))) ≅ RR₁(RG₀(M))` of the two readings of the target.

## Main results

* `Stacks.Cohomology.BaseChange.mapPlus_pasteSource_app`: the pasting identity applied
  degreewise to a bounded below complex.
* `Stacks.Cohomology.BaseChange.onHomotopy_pasteSource_app`: **the pasting identity for
  `onHomotopy`**, valid at every bounded below complex.
* `Stacks.Cohomology.BaseChange.isIso_derived_app_pasteSource`: **the transfer of
  invertibility** — the lower square's descent is invertible at `Qh(E K)`.

## References

* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

universe u₀ u₁ u₂ u₃ u₄ u₅ v₀ v₁ v₂ v₃ v₄ v₅ w₀ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The pasting identity applied degreewise -/

section Degreewise

variable {A₀ : Type u₀} {A : Type u₁} {B : Type u₂} {C₀ : Type u₃} {C : Type u₄} {D : Type u₅}
  [Category.{v₀} A₀] [Category.{v₁} A] [Category.{v₂} B]
  [Category.{v₃} C₀] [Category.{v₄} C] [Category.{v₅} D]
  [Preadditive A₀] [Preadditive A] [Preadditive B]
  [Preadditive C₀] [Preadditive C] [Preadditive D]
  (E : A₀ ⥤ A) (F : A ⥤ B) (E' : C₀ ⥤ C) (F' : C ⥤ D)
  (G : B ⥤ D) (G' : A ⥤ C) (G'' : A₀ ⥤ C₀) (R₀ : A₀ ⥤ B) (R₁ : C₀ ⥤ D) (G₀ : A₀ ⥤ C₀)
  [E.Additive] [F.Additive] [E'.Additive] [F'.Additive]
  [G.Additive] [G'.Additive] [G''.Additive] [R₀.Additive] [R₁.Additive] [G₀.Additive]
  (τ' : E ⋙ G' ⟶ G'' ⋙ E') (τ : F ⋙ G ⟶ G' ⋙ F') (ρ : R₀ ⋙ G ⟶ G₀ ⋙ R₁)
  (cR : E ⋙ F ≅ R₀) (cR' : E' ⋙ F' ≅ R₁) (cG : G'' ≅ G₀)

/-- **The pasting identity along the fibre, applied degreewise to a complex.** The hypothesis is
the identity at each object of `A₀`; the conclusion is the same identity for the induced
transformations on complexes, where it holds in every degree. -/
theorem paste_mapHomologicalComplex_source_app {ι : Type*} (c : ComplexShape ι)
    (hρ : ∀ M, ρ.app M = G.map (cR.inv.app M) ≫ τ.app (E.obj M) ≫ F'.map (τ'.app M) ≫
      F'.map (E'.map (cG.hom.app M)) ≫ cR'.hom.app (G₀.obj M))
    (L : HomologicalComplex A₀ c) :
    (NatTrans.mapHomologicalComplex ρ c).app L =
      (G.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex cR.inv c).app L) ≫
        (NatTrans.mapHomologicalComplex τ c).app ((E.mapHomologicalComplex c).obj L) ≫
          (F'.mapHomologicalComplex c).map
            ((NatTrans.mapHomologicalComplex τ' c).app L) ≫
            (F'.mapHomologicalComplex c).map ((E'.mapHomologicalComplex c).map
              ((NatTrans.mapHomologicalComplex cG.hom c).app L)) ≫
              (NatTrans.mapHomologicalComplex cR'.hom c).app
                ((G₀.mapHomologicalComplex c).obj L) := by
  ext i
  simpa using hρ (L.X i)

/-- **The pasting identity along the fibre on the homotopy category.** -/
theorem paste_mapHomotopyCategory_source_app {ι : Type*} (c : ComplexShape ι)
    (hρ : ∀ M, ρ.app M = G.map (cR.inv.app M) ≫ τ.app (E.obj M) ≫ F'.map (τ'.app M) ≫
      F'.map (E'.map (cG.hom.app M)) ≫ cR'.hom.app (G₀.obj M))
    (M : HomotopyCategory A₀ c) :
    (NatTrans.mapHomotopyCategory ρ c).app M =
      (G.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory cR.inv c).app M) ≫
        (NatTrans.mapHomotopyCategory τ c).app ((E.mapHomotopyCategory c).obj M) ≫
          (F'.mapHomotopyCategory c).map
            ((NatTrans.mapHomotopyCategory τ' c).app M) ≫
            (F'.mapHomotopyCategory c).map ((E'.mapHomotopyCategory c).map
              ((NatTrans.mapHomotopyCategory cG.hom c).app M)) ≫
              (NatTrans.mapHomotopyCategory cR'.hom c).app
                ((G₀.mapHomotopyCategory c).obj M) := by
  obtain ⟨L⟩ := M
  refine Eq.trans (congrArg (fun z => (HomotopyCategory.quotient D c).map z)
    (paste_mapHomologicalComplex_source_app E F E' F' G G' G'' R₀ R₁ G₀ τ' τ ρ cR cR' cG
      c hρ L)) ?_
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  rfl

end Degreewise

/-! ### The pasting identity on the bounded below homotopy category -/

section Plus

variable {A₀ : Type u₀} {A : Type u₁} {B : Type u₂} {C₀ : Type u₃} {C : Type u₄} {D : Type u₅}
  [Category.{v₀} A₀] [Category.{v₁} A] [Category.{v₂} B]
  [Category.{v₃} C₀] [Category.{v₄} C] [Category.{v₅} D]
  [Abelian A₀] [Abelian A] [Abelian B] [Abelian C₀] [Abelian C] [Abelian D]
  (E : A₀ ⥤ A) (F : A ⥤ B) (E' : C₀ ⥤ C) (F' : C ⥤ D)
  (G : B ⥤ D) (G' : A ⥤ C) (G'' : A₀ ⥤ C₀) (R₀ : A₀ ⥤ B) (R₁ : C₀ ⥤ D) (G₀ : A₀ ⥤ C₀)
  [E.Additive] [F.Additive] [E'.Additive] [F'.Additive]
  [G.Additive] [G'.Additive] [G''.Additive] [R₀.Additive] [R₁.Additive] [G₀.Additive]
  (τ' : E ⋙ G' ⟶ G'' ⋙ E') (τ : F ⋙ G ⟶ G' ⋙ F') (ρ : R₀ ⋙ G ⟶ G₀ ⋙ R₁)
  (cR : E ⋙ F ≅ R₀) (cR' : E' ⋙ F' ≅ R₁) (cG : G'' ≅ G₀)

/-- **The pasting identity along the fibre, degreewise on the bounded below homotopy
category.** -/
theorem mapPlus_pasteSource_app
    (hρ : ∀ M, ρ.app M = G.map (cR.inv.app M) ≫ τ.app (E.obj M) ≫ F'.map (τ'.app M) ≫
      F'.map (E'.map (cG.hom.app M)) ≫ cR'.hom.app (G₀.obj M))
    (K : HomotopyCategory.Plus A₀) :
    (mapPlus ρ).app K =
      G.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusCompIso cR).inv.app K) ≫
        (mapPlus τ).app (E.mapHomotopyCategoryPlus.obj K) ≫
          F'.mapHomotopyCategoryPlus.map ((mapPlus τ').app K) ≫
            F'.mapHomotopyCategoryPlus.map
              (E'.mapHomotopyCategoryPlus.map ((mapPlus cG.hom).app K)) ≫
              (Functor.mapHomotopyCategoryPlusCompIso cR').hom.app
                (G₀.mapHomotopyCategoryPlus.obj K) := by
  ext
  exact paste_mapHomotopyCategory_source_app E F E' F' G G' G'' R₀ R₁ G₀ τ' τ ρ cR cR' cG
    (ComplexShape.up ℤ) hρ K.obj

end Plus

/-! ### The two readings of the target -/

section Target

variable {C₀ : Type u₃} {C : Type u₄} {D : Type u₅}
  [Category.{v₃} C₀] [Category.{v₄} C] [Category.{v₅} D]
  [Abelian C₀] [Abelian C] [Abelian D] [EnoughInjectives C₀] [EnoughInjectives C]

/-- An isomorphism of additive functors is, degreewise, `mapPlus` of its `hom`. -/
theorem mapHomotopyCategoryPlusNatIso_hom_app {A : Type u₀} [Category.{v₀} A] [Abelian A]
    {E H : A ⥤ C₀} [E.Additive] [H.Additive] (e : E ≅ H) (K : HomotopyCategory.Plus A) :
    (Functor.mapHomotopyCategoryPlusNatIso e).hom.app K = (mapPlus e.hom).app K :=
  rfl

/-- The comparison for a composite agrees with the degreewise image of the comparison of the
two composite legs. -/
theorem mapHomotopyCategoryPlusCompIso_hom_app_eq (E' : C₀ ⥤ C) (F' : C ⥤ D) (R₁ : C₀ ⥤ D)
    [E'.Additive] [F'.Additive] [R₁.Additive] (cR' : E' ⋙ F' ≅ R₁)
    (K : HomotopyCategory.Plus C₀) :
    (Functor.mapHomotopyCategoryPlusCompIso cR').hom.app K =
      (Functor.mapHomotopyCategoryPlusNatIso cR').hom.app K :=
  rfl

end Target

/-! ### The shape of the chase over the target -/

/-- **The shape of the chase over the target, in an arbitrary category.**  A sixfold composite
whose first two factors are rewritten by `h₁`, whose third crosses a naturality square `h₂`,
whose fourth cancels by `h₃`, whose fifth crosses a naturality square `h₄` and whose remaining
two are rewritten by `h₅` and `h₆`, is the fourfold composite `p ≫ q ≫ r ≫ s`. -/
private theorem targetChase {𝒞 : Type*} [Category* 𝒞]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ Y₁ Y₂ Z₅ Z₆ : 𝒞}
    {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {d : X₃ ⟶ X₄} {e : X₄ ⟶ X₅} {k : X₅ ⟶ X₆}
    {α : X₀ ⟶ Y₂} {β : Y₂ ⟶ X₂} {γ : Y₂ ⟶ X₄} {δ : X₄ ⟶ X₃}
    {ε : Y₂ ⟶ Z₅} {ζ : Z₅ ⟶ X₅} {p : X₀ ⟶ Y₁} {q : Y₁ ⟶ Z₅} {r : Z₅ ⟶ Z₆} {s : Z₆ ⟶ X₆}
    (h₁ : a ≫ b = α ≫ β) (h₂ : β ≫ c = γ ≫ δ) (h₃ : δ ≫ d = 𝟙 X₄)
    (h₄ : γ ≫ e = ε ≫ ζ) (h₅ : α ≫ ε = p ≫ q) (h₆ : ζ ≫ k = r ≫ s) :
    a ≫ b ≫ c ≫ d ≫ e ≫ k = p ≫ q ≫ r ≫ s := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₆, reassoc_of% h₅]

/-! ### The pasting identity for `onHomotopy` -/

section OnHomotopy

variable {A₀ : Type u₀} {A : Type u₁} {B : Type u₂} {C₀ : Type u₃} {C : Type u₄} {D : Type u₅}
  [Category.{v₀} A₀] [Category.{v₁} A] [Category.{v₂} B]
  [Category.{v₃} C₀] [Category.{v₄} C] [Category.{v₅} D]
  [Abelian A₀] [Abelian A] [Abelian B] [Abelian C₀] [Abelian C] [Abelian D]
  [EnoughInjectives A₀] [EnoughInjectives A] [EnoughInjectives B]
  [EnoughInjectives C₀] [EnoughInjectives C]
  (E : A₀ ⥤ A) (F : A ⥤ B) (E' : C₀ ⥤ C) (F' : C ⥤ D)
  (G : B ⥤ D) (G' : A ⥤ C) (G'' : A₀ ⥤ C₀) (R₀ : A₀ ⥤ B) (R₁ : C₀ ⥤ D) (G₀ : A₀ ⥤ C₀)
  [E.Additive] [F.Additive] [E'.Additive] [F'.Additive]
  [G.Additive] [G'.Additive] [G''.Additive] [R₀.Additive] [R₁.Additive] [G₀.Additive]
  [E'.PreservesInjectiveObjects]

/-- **The comparison of the two readings of the target of the pasted comparison**: the
composition isomorphism for `RE'` and `RF'`, the invariance of right derivation under the
isomorphism `cR'`, and the invariance under `cG`. -/
def pasteSourceTargetIso (cR' : E' ⋙ F' ≅ R₁) (cG : G'' ≅ G₀) :
    G''.rightDerivedFunctorPlus ⋙ E'.rightDerivedFunctorPlus ⋙ F'.rightDerivedFunctorPlus ≅
      G₀.rightDerivedFunctorPlus ⋙ R₁.rightDerivedFunctorPlus :=
  Functor.isoWhiskerLeft G''.rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusCompIso E' F').symm ≪≫
    Functor.isoWhiskerLeft G''.rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusNatIso cR') ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorPlusNatIso cG)
      R₁.rightDerivedFunctorPlus

/-- The component of `pasteSourceTargetIso` at `M`, as the composite of its three factors: the
inverse of the composition isomorphism for `RE'` and `RF'`, the invariance of right derivation
under `cR'`, and the image under `RR₁` of the invariance under `cG`. -/
theorem pasteSourceTargetIso_hom_app (cR' : E' ⋙ F' ≅ R₁) (cG : G'' ≅ G₀)
    (M : DerivedCategory.Plus A₀) :
    (pasteSourceTargetIso E' F' G'' R₁ G₀ cR' cG).hom.app M =
      (Functor.rightDerivedFunctorPlusCompIso E' F').inv.app
          (G''.rightDerivedFunctorPlus.obj M) ≫
        (Functor.rightDerivedFunctorPlusNatIso cR').hom.app
          (G''.rightDerivedFunctorPlus.obj M) ≫
        R₁.rightDerivedFunctorPlus.map
          ((Functor.rightDerivedFunctorPlusNatIso cG).hom.app M) := by
  simp [pasteSourceTargetIso]

/-- The part of the pasting identity that lives over the target: the iterated derived-functor
unit of `RE'` and `RF'`, read through the comparison of the two readings of the target, is the
derived-functor unit of `RR₁` preceded by the degreewise comparisons. -/
theorem unit_comp_pasteSourceTargetIso (cR' : E' ⋙ F' ≅ R₁) (cG : G'' ≅ G₀)
    (K : HomotopyCategory.Plus A₀) :
    F'.rightDerivedFunctorPlusUnit.app
          (E'.mapHomotopyCategoryPlus.obj (G''.mapHomotopyCategoryPlus.obj K)) ≫
        F'.rightDerivedFunctorPlus.map
          (E'.rightDerivedFunctorPlusUnit.app (G''.mapHomotopyCategoryPlus.obj K)) ≫
        F'.rightDerivedFunctorPlus.map (E'.rightDerivedFunctorPlus.map
          (G''.rightDerivedFunctorPlusUnit.app K)) ≫
        (pasteSourceTargetIso E' F' G'' R₁ G₀ cR' cG).hom.app
          (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso cR').hom.app
            (G''.mapHomotopyCategoryPlus.obj K)) ≫
        R₁.rightDerivedFunctorPlusUnit.app (G''.mapHomotopyCategoryPlus.obj K) ≫
        R₁.rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Qh.map ((mapPlus cG.hom).app K)) ≫
          R₁.rightDerivedFunctorPlus.map (G₀.rightDerivedFunctorPlusUnit.app K) := by
  have hA : F'.rightDerivedFunctorPlusUnit.app
        (E'.mapHomotopyCategoryPlus.obj (G''.mapHomotopyCategoryPlus.obj K)) ≫
      F'.rightDerivedFunctorPlus.map
        (E'.rightDerivedFunctorPlusUnit.app (G''.mapHomotopyCategoryPlus.obj K)) =
      (E' ⋙ F').rightDerivedFunctorPlusUnit.app (G''.mapHomotopyCategoryPlus.obj K) ≫
        (Functor.rightDerivedFunctorPlusComp E' F').app
          (DerivedCategory.Plus.Qh.obj (G''.mapHomotopyCategoryPlus.obj K)) := by
    rw [Functor.rightDerivedFunctorPlusComp_fac_app,
      map_mapHomotopyCategoryPlusCompIso_inv_app E' F' DerivedCategory.Plus.Qh
        (G''.mapHomotopyCategoryPlus.obj K)]
    exact (Category.id_comp _).symm
  have hE := unit_comp_rightDerivedFunctorPlusNatIso_hom cG K
  rw [pasteSourceTargetIso_hom_app]
  refine targetChase hA
    ((Functor.rightDerivedFunctorPlusComp E' F').naturality
      (G''.rightDerivedFunctorPlusUnit.app K)).symm
    ((Functor.rightDerivedFunctorPlusCompIso E' F').hom_inv_id_app _)
    ((Functor.rightDerivedFunctorPlusNatIso cR').hom.naturality
      (G''.rightDerivedFunctorPlusUnit.app K))
    (unit_comp_rightDerivedFunctorPlusNatIso_hom cR'
      (G''.mapHomotopyCategoryPlus.obj K)) ?_
  rw [← Functor.map_comp, hE, Functor.map_comp]
  rfl

end OnHomotopy

/-! ### The shapes of the two remaining chases -/

/-- **The shape of the chase over the suffix, in an arbitrary category.** -/
private theorem suffixChase {𝒞 : Type*} [Category* 𝒞]
    {x₀ x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ z₁ z₂ w₁ w₂ : 𝒞}
    {L₁ : x₀ ⟶ x₁} {L₂ : x₁ ⟶ x₂} {L₃ : x₂ ⟶ x₃} {L₄ : x₃ ⟶ x₄} {L₅ : x₄ ⟶ x₅}
    {R₁' : x₀ ⟶ y₁} {R₂ : y₁ ⟶ y₂} {R₃ : y₂ ⟶ y₃} {R₄ : y₃ ⟶ x₅}
    {m : x₁ ⟶ z₁} {n : y₁ ⟶ z₁} {o₁ : z₁ ⟶ z₂} {o₂ : z₂ ⟶ y₃}
    {c : x₁ ⟶ w₁} {d : w₁ ⟶ w₂} {e : w₂ ⟶ x₄} {g : w₁ ⟶ x₃}
    (h₁ : R₂ ≫ R₃ = n ≫ o₁ ≫ o₂) (h₂ : R₁' ≫ n = L₁ ≫ m)
    (h₃ : m ≫ o₁ ≫ o₂ ≫ R₄ = c ≫ d ≫ e ≫ L₅)
    (h₄ : L₂ ≫ L₃ = c ≫ g) (h₅ : g ≫ L₄ = d ≫ e) :
    L₁ ≫ L₂ ≫ L₃ ≫ L₄ ≫ L₅ = R₁' ≫ R₂ ≫ R₃ ≫ R₄ := by
  calc L₁ ≫ L₂ ≫ L₃ ≫ L₄ ≫ L₅ = L₁ ≫ c ≫ g ≫ L₄ ≫ L₅ := by rw [reassoc_of% h₄]
    _ = L₁ ≫ c ≫ d ≫ e ≫ L₅ := by rw [reassoc_of% h₅]
    _ = R₁' ≫ R₂ ≫ R₃ ≫ R₄ := by rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- **The shape of the gluing of the prefix to the suffix, in an arbitrary category.** -/
private theorem glueChase {𝒞 : Type*} [Category* 𝒞]
    {n₀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ m₁ m₂ q₁ q₂ : 𝒞}
    {lhs : n₀ ⟶ n₈} {a₁ : n₀ ⟶ n₁} {u : n₁ ⟶ n₆} {a₇ : n₆ ⟶ n₇} {a₈ : n₇ ⟶ n₈}
    {a₂ : n₁ ⟶ n₂} {a₃ : n₂ ⟶ n₃} {a₄ : n₃ ⟶ n₄} {a₅ : n₄ ⟶ n₅} {a₆ : n₅ ⟶ n₆}
    {b₁ : n₀ ⟶ m₁} {a₁' : m₁ ⟶ n₂} {v : m₁ ⟶ m₂} {c₁ : n₃ ⟶ q₁} {c₂ : q₁ ⟶ m₂}
    {r₃ : m₂ ⟶ q₂} {r₄ : q₂ ⟶ n₈}
    (h₁ : lhs = a₁ ≫ u ≫ a₇ ≫ a₈) (h₂ : u = a₂ ≫ a₃ ≫ a₄ ≫ a₅ ≫ a₆)
    (h₃ : a₁ ≫ a₂ = b₁ ≫ a₁') (h₄ : v = a₁' ≫ a₃ ≫ c₁ ≫ c₂)
    (h₅ : a₄ ≫ a₅ ≫ a₆ ≫ a₇ ≫ a₈ = c₁ ≫ c₂ ≫ r₃ ≫ r₄) :
    lhs = b₁ ≫ v ≫ r₃ ≫ r₄ := by
  rw [h₁, h₂, h₄]
  simp only [Category.assoc]
  rw [h₅, reassoc_of% h₃]

/-- A functor applied to a threefold composite. -/
private theorem map_comp₃ {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {o₁ o₂ o₃ o₄ : 𝒞} (a : o₁ ⟶ o₂) (b : o₂ ⟶ o₃) (c : o₃ ⟶ o₄) :
    Φ.map (a ≫ b ≫ c) = Φ.map a ≫ Φ.map b ≫ Φ.map c := by
  rw [Φ.map_comp, Φ.map_comp]

/-- A functor applied to a fivefold composite. -/
private theorem map_comp₅ {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {o₁ o₂ o₃ o₄ o₅ o₆ : 𝒞} (a : o₁ ⟶ o₂) (b : o₂ ⟶ o₃) (c : o₃ ⟶ o₄) (d : o₄ ⟶ o₅)
    (e : o₅ ⟶ o₆) :
    Φ.map (a ≫ b ≫ c ≫ d ≫ e) = Φ.map a ≫ Φ.map b ≫ Φ.map c ≫ Φ.map d ≫ Φ.map e := by
  rw [Φ.map_comp, Φ.map_comp, Φ.map_comp, Φ.map_comp]

/-! ### The pasting identity for `onHomotopy` -/

section Paste

variable {A₀ : Type u₀} {A : Type u₁} {B : Type u₂} {C₀ : Type u₃} {C : Type u₄} {D : Type u₅}
  [Category.{v₀} A₀] [Category.{v₁} A] [Category.{v₂} B]
  [Category.{v₃} C₀] [Category.{v₄} C] [Category.{v₅} D]
  [Abelian A₀] [Abelian A] [Abelian B] [Abelian C₀] [Abelian C] [Abelian D]
  [EnoughInjectives A₀] [EnoughInjectives A] [EnoughInjectives B]
  [EnoughInjectives C₀] [EnoughInjectives C]
  (E : A₀ ⥤ A) (F : A ⥤ B) (E' : C₀ ⥤ C) (F' : C ⥤ D)
  (G : B ⥤ D) (G' : A ⥤ C) (G'' : A₀ ⥤ C₀) (R₀ : A₀ ⥤ B) (R₁ : C₀ ⥤ D) (G₀ : A₀ ⥤ C₀)
  [E.Additive] [F.Additive] [E'.Additive] [F'.Additive]
  [G.Additive] [G'.Additive] [G''.Additive] [R₀.Additive] [R₁.Additive] [G₀.Additive]
  [E'.PreservesInjectiveObjects]
  (τ' : E ⋙ G' ⟶ G'' ⋙ E') (τ : F ⋙ G ⟶ G' ⋙ F') (ρ : R₀ ⋙ G ⟶ G₀ ⋙ R₁)
  (cR : E ⋙ F ≅ R₀) (cR' : E' ⋙ F' ≅ R₁) (cG : G'' ≅ G₀)
  (eU : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)
  (eV : G'.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ G'.rightDerivedFunctorPlus)

/-- The suffix of the pasting identity: everything after the degreewise comparison of the lower
square. -/
private theorem onHomotopy_pasteSource_suffix (hV : eV.hom = G'.rightDerivedFunctorPlusUnit)
    (K : HomotopyCategory.Plus A₀) :
    DerivedCategory.Plus.Qh.map
          (F'.mapHomotopyCategoryPlus.map ((mapPlus τ').app K)) ≫
        DerivedCategory.Plus.Qh.map (F'.mapHomotopyCategoryPlus.map
          (E'.mapHomotopyCategoryPlus.map ((mapPlus cG.hom).app K))) ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso cR').hom.app
            (G₀.mapHomotopyCategoryPlus.obj K)) ≫
        R₁.rightDerivedFunctorPlusUnit.app (G₀.mapHomotopyCategoryPlus.obj K) ≫
        R₁.rightDerivedFunctorPlus.map (G₀.rightDerivedFunctorPlusUnit.app K) =
      F'.rightDerivedFunctorPlusUnit.app
          (G'.mapHomotopyCategoryPlus.obj (E.mapHomotopyCategoryPlus.obj K)) ≫
        F'.rightDerivedFunctorPlus.map
          (G'.rightDerivedFunctorPlusUnit.app (E.mapHomotopyCategoryPlus.obj K)) ≫
        F'.rightDerivedFunctorPlus.map ((onHomotopy E E' G' G'' τ' eV).app K) ≫
        (pasteSourceTargetIso E' F' G'' R₁ G₀ cR' cG).hom.app
          (DerivedCategory.Plus.Qh.obj K) := by
  have hcancel : G'.rightDerivedFunctorPlusUnit.app (E.mapHomotopyCategoryPlus.obj K) ≫
      eV.inv.app (E.mapHomotopyCategoryPlus.obj K) = 𝟙 _ := by
    rw [← hV]
    exact eV.hom_inv_id_app _
  have hmid : G'.rightDerivedFunctorPlusUnit.app (E.mapHomotopyCategoryPlus.obj K) ≫
      (onHomotopy E E' G' G'' τ' eV).app K =
      DerivedCategory.Plus.Qh.map ((mapPlus τ').app K) ≫
        E'.rightDerivedFunctorPlusUnit.app (G''.mapHomotopyCategoryPlus.obj K) ≫
        E'.rightDerivedFunctorPlus.map (G''.rightDerivedFunctorPlusUnit.app K) := by
    rw [onHomotopy_app, ← Category.assoc, hcancel, Category.id_comp]
    rfl
  have hwhisker : F'.rightDerivedFunctorPlus.map
          (G'.rightDerivedFunctorPlusUnit.app (E.mapHomotopyCategoryPlus.obj K)) ≫
        F'.rightDerivedFunctorPlus.map ((onHomotopy E E' G' G'' τ' eV).app K) =
      F'.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map ((mapPlus τ').app K)) ≫
        F'.rightDerivedFunctorPlus.map
          (E'.rightDerivedFunctorPlusUnit.app (G''.mapHomotopyCategoryPlus.obj K)) ≫
        F'.rightDerivedFunctorPlus.map (E'.rightDerivedFunctorPlus.map
          (G''.rightDerivedFunctorPlusUnit.app K)) := by
    rw [← Functor.map_comp, hmid]
    exact map_comp₃ _ _ _ _
  have hnat : DerivedCategory.Plus.Qh.map (F'.mapHomotopyCategoryPlus.map
          (E'.mapHomotopyCategoryPlus.map ((mapPlus cG.hom).app K))) ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso cR').hom.app
            (G₀.mapHomotopyCategoryPlus.obj K)) =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso cR').hom.app
            (G''.mapHomotopyCategoryPlus.obj K)) ≫
        DerivedCategory.Plus.Qh.map (R₁.mapHomotopyCategoryPlus.map
          ((mapPlus cG.hom).app K)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusCompIso cR').hom.naturality ((mapPlus cG.hom).app K))
  exact suffixChase hwhisker
    (F'.rightDerivedFunctorPlusUnit.naturality ((mapPlus τ').app K)).symm
    (unit_comp_pasteSourceTargetIso E' F' G'' R₁ G₀ cR' cG K) hnat
    (R₁.rightDerivedFunctorPlusUnit.naturality ((mapPlus cG.hom).app K))

/-- **The pasting identity along the fibre for `onHomotopy`.**  It holds at every bounded below
complex: no injectivity and no acyclicity enter, only naturality, the comparisons of right
derived functors, and the hypothesis that `eV` is the derived-functor unit of `RG'`. -/
theorem onHomotopy_pasteSource_app (hV : eV.hom = G'.rightDerivedFunctorPlusUnit)
    (hρ : ∀ M, ρ.app M = G.map (cR.inv.app M) ≫ τ.app (E.obj M) ≫ F'.map (τ'.app M) ≫
      F'.map (E'.map (cG.hom.app M)) ≫ cR'.hom.app (G₀.obj M))
    (K : HomotopyCategory.Plus A₀) :
    (onHomotopy R₀ R₁ G G₀ ρ eU).app K =
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso cR).inv.app K)) ≫
        (onHomotopy F F' G G' τ eU).app (E.mapHomotopyCategoryPlus.obj K) ≫
        F'.rightDerivedFunctorPlus.map ((onHomotopy E E' G' G'' τ' eV).app K) ≫
        (pasteSourceTargetIso E' F' G'' R₁ G₀ cR' cG).hom.app
          (DerivedCategory.Plus.Qh.obj K) := by
  have p₁ : (onHomotopy R₀ R₁ G G₀ ρ eU).app K =
      eU.inv.app (R₀.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
          (G.mapHomotopyCategoryPlus.map
              ((Functor.mapHomotopyCategoryPlusCompIso cR).inv.app K) ≫
            (mapPlus τ).app (E.mapHomotopyCategoryPlus.obj K) ≫
            F'.mapHomotopyCategoryPlus.map ((mapPlus τ').app K) ≫
            F'.mapHomotopyCategoryPlus.map
              (E'.mapHomotopyCategoryPlus.map ((mapPlus cG.hom).app K)) ≫
            (Functor.mapHomotopyCategoryPlusCompIso cR').hom.app
              (G₀.mapHomotopyCategoryPlus.obj K)) ≫
        R₁.rightDerivedFunctorPlusUnit.app (G₀.mapHomotopyCategoryPlus.obj K) ≫
        R₁.rightDerivedFunctorPlus.map (G₀.rightDerivedFunctorPlusUnit.app K) := by
    rw [onHomotopy_app R₀ R₁ G G₀ ρ eU K,
      mapPlus_pasteSource_app E F E' F' G G' G'' R₀ R₁ G₀ τ' τ ρ cR cR' cG hρ K]
    rfl
  exact glueChase p₁ (map_comp₅ DerivedCategory.Plus.Qh _ _ _ _ _)
    (eU.inv.naturality ((Functor.mapHomotopyCategoryPlusCompIso cR).inv.app K)).symm
    (onHomotopy_app F F' G G' τ eU (E.mapHomotopyCategoryPlus.obj K))
    (onHomotopy_pasteSource_suffix E E' F' G' G'' R₁ G₀ τ' cR' cG eV hV K)

/-- The derived-functor unit is invertible at a bounded below complex of injective objects. -/
private theorem isIso_unit_app_of_injective {A' B' : Type*} [Category* A'] [Category* B']
    [Abelian A'] [Abelian B'] [EnoughInjectives A'] (Φ : A' ⥤ B') [Φ.Additive]
    (K : HomotopyCategory.Plus A') (hK : ∀ n : ℤ, Injective (K.obj.as.X n)) :
    IsIso (Φ.rightDerivedFunctorPlusUnit.app K) := by
  refine Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun n => ?_
  have := hK n
  exact Functor.rightAcyclic_of_injective _ _

/-- If the derived-functor unit of `F` is invertible at `K`, the `onHomotopy` comparison is
invertible at `K` exactly when the descended comparison is invertible at `Qh K`. -/
private theorem isIso_onHomotopy_app_iff {A' B' C' D' : Type*} [Category* A'] [Category* B']
    [Category* C'] [Category* D'] [Abelian A'] [Abelian B'] [Abelian C'] [Abelian D']
    [EnoughInjectives A'] [EnoughInjectives B'] [EnoughInjectives C']
    (F₁ : A' ⥤ B') (F₂ : C' ⥤ D') (G₁ : B' ⥤ D') (G₂ : A' ⥤ C')
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive] (τ₁ : F₁ ⋙ G₁ ⟶ G₂ ⋙ F₂)
    (e₁ : G₁.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G₁.rightDerivedFunctorPlus)
    (K : HomotopyCategory.Plus A') [IsIso (F₁.rightDerivedFunctorPlusUnit.app K)] :
    IsIso ((onHomotopy F₁ F₂ G₁ G₂ τ₁ e₁).app K) ↔
      IsIso ((derived F₁ F₂ G₁ G₂ τ₁ e₁).app (DerivedCategory.Plus.Qh.obj K)) := by
  rw [← derived_fac_app F₁ F₂ G₁ G₂ τ₁ e₁ K]
  exact ⟨fun h => IsIso.of_isIso_comp_left
    (G₁.rightDerivedFunctorPlus.map (F₁.rightDerivedFunctorPlusUnit.app K)) _,
    fun h => inferInstance⟩

/-- **The transfer of invertibility along the fibre-direction pasting.**  Let `K` be a bounded
below complex of injective objects of `A₀` and suppose the descended comparisons of the
rectangle and of the upper square are invertible at its image in `D⁺(A₀)`.  Then the descended
comparison of the lower square is invertible at the image of `E K`.

The pasting identity `onHomotopy_pasteSource_app` exhibits the rectangle's `onHomotopy` as a
fourfold composite whose factors other than the lower square's `onHomotopy` are invertible, and
`Stacks.Cohomology.BaseChange.derived_fac_app` identifies each `onHomotopy` with the
corresponding descent, the derived-functor units being invertible on complexes of
injectives. -/
theorem isIso_derived_app_pasteSource [E.PreservesInjectiveObjects]
    (hV : eV.hom = G'.rightDerivedFunctorPlusUnit)
    (hρ : ∀ M, ρ.app M = G.map (cR.inv.app M) ≫ τ.app (E.obj M) ≫ F'.map (τ'.app M) ≫
      F'.map (E'.map (cG.hom.app M)) ≫ cR'.hom.app (G₀.obj M))
    (K : HomotopyCategory.Plus A₀) (hK : ∀ n : ℤ, Injective (K.obj.as.X n))
    (hrect : IsIso ((derived R₀ R₁ G G₀ ρ eU).app (DerivedCategory.Plus.Qh.obj K)))
    (hup : IsIso ((derived E E' G' G'' τ' eV).app (DerivedCategory.Plus.Qh.obj K))) :
    IsIso ((derived F F' G G' τ eU).app
      (DerivedCategory.Plus.Qh.obj (E.mapHomotopyCategoryPlus.obj K))) := by
  have hKE : ∀ n : ℤ, Injective ((E.mapHomotopyCategoryPlus.obj K).obj.as.X n) := fun n => by
    have := hK n
    exact inferInstanceAs (Injective (E.obj (K.obj.as.X n)))
  have := isIso_unit_app_of_injective R₀ K hK
  have := isIso_unit_app_of_injective E K hK
  have := isIso_unit_app_of_injective F (E.mapHomotopyCategoryPlus.obj K) hKE
  -- the rectangle's and the upper square's `onHomotopy` are invertible
  have := (isIso_onHomotopy_app_iff E E' G' G'' τ' eV K).2 hup
  have : IsIso (F'.rightDerivedFunctorPlus.map ((onHomotopy E E' G' G'' τ' eV).app K)) :=
    Functor.map_isIso _ _
  have : IsIso ((pasteSourceTargetIso E' F' G'' R₁ G₀ cR' cG).hom.app
      (DerivedCategory.Plus.Qh.obj K)) := inferInstance
  have : IsIso (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusCompIso cR).inv.app K))) :=
    Functor.map_isIso _ _
  have h := (isIso_onHomotopy_app_iff R₀ R₁ G G₀ ρ eU K).2 hrect
  rw [onHomotopy_pasteSource_app E F E' F' G G' G'' R₀ R₁ G₀ τ' τ ρ cR cR' cG eU eV hV hρ K] at h
  exact (isIso_onHomotopy_app_iff F F' G G' τ eU _).1
    ((isIso_comp_right_iff _ _).1 ((isIso_comp_left_iff _ _).1 h))

end Paste

end Stacks.Cohomology.BaseChange

end
