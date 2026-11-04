module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeFunctoriality

/-!
# The cone of a morphism is a pushout of the cone on the identity

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of differential graded `R`-algebras and
let `f : K ⟶ L` be a morphism of right differential graded `A`-modules. The square

```
      K  ------ f ------> L
      |                   |
  ι_K |                   | inclusion of the cone of f
      v                   v
  cone (𝟙 K) -- φ --> cone f
```

whose vertical arrows are the canonical inclusions of the two cones and whose lower horizontal
arrow is the functoriality of the cone applied to the commutative square `(𝟙 K, f)`, is a
pushout. Degreewise it is the square

```
      K^n ----- f^n -----> L^n
       |                    |
  inr  |                    | inr
       v                    v
 K^{n+1} ⊞ K^n -- (𝟙, f^n) --> K^{n+1} ⊞ L^n
```

in sheaves of modules, which is a pushout because the first summand is carried over untouched
while the second is the given morphism.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ConePackage.fromConeId`: the morphism
  `cone (𝟙 K) ⟶ cone f` induced by the commutative square `(𝟙 K, f)`.
* `SheafOfModules.DifferentialGradedModule.ConePackage.pushoutDesc`: the morphism out of the cone
  of `f` produced by a morphism out of the cone of `𝟙 K` and a morphism out of `L` which agree
  on `K`.

## Main results

* `SheafOfModules.DifferentialGradedModule.ConePackage.isColimitPushoutCocone`: **the cone of
  `f` is a colimit of the span `cone (𝟙 K) ⟵ K ⟶ L`**, the two legs being the canonical
  inclusion of the cone of `𝟙 K` and `f`.
* `SheafOfModules.DifferentialGradedModule.ConePackage.isPushout`: the same statement as
  `CategoryTheory.IsPushout`, for the square above.
* `SheafOfModules.DifferentialGradedModule.ConePackage.coneSectionX_d`: the section of a cone's
  projection, composed with the cone's differential, is the differential of the shift followed by
  the section plus the identification of the first summand followed by the cone's inclusion.
* `SheafOfModules.DifferentialGradedModule.ConePackage.d_coneRetractionX`: the cone's
  differential, read in the second coordinate of the degreewise splitting.

## Implementation notes

The descent morphism is written without choosing a pushout and without an abelian structure, so
no hypothesis on the site is needed. Degreewise it is

`p ≫ s ≫ h + r ≫ k`,

where `p : cone f ⟶ K[1]` is the cone's projection, `s : K[1] ⟶ cone (𝟙 K)` and
`r : cone f ⟶ L` are the two coordinate maps of the degreewise splittings recorded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConeAdmissible.lean`, and `h`,
`k` are the two morphisms out of the span. Compatibility with the right action of the algebra is
immediate in that spelling: `p`, `h` and `k` are morphisms of differential graded modules, and
`s` and `r` commute with the action by `ConePackage.coneSectionX_action_fst`,
`ConePackage.coneSectionX_action_snd` and `ConePackage.action_second`. No degree is shifted
along the way, so none of the transports `SheafOfModules.castHom` of the module laws appears.

That the degreewise family is a morphism of complexes is the one computation of substance. It
uses the differential of a cone in the two coordinates of its splitting: in the first through the
projection, which is a morphism of complexes, and in the second through
`ConePackage.d_coneRetractionX`, which reads Mathlib's
`HomologicalComplex.homotopyCofiber.d_sndX` through the data of a cone package.

Both the factorisation and its uniqueness come from the identity
`ConePackage.coneRetractionX_inclusion_add`, which decomposes the identity of a cone into the two
coordinates of its splitting.

## References

* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {K L : DifferentialGradedModule.{t, a, m} A}

namespace ConePackage

variable {f : K ⟶ L}

/-! ### The differential and the two coordinates of the degreewise splitting -/

/-- **The differential of a cone, read in the second coordinate of its degreewise splitting**:
it is the first coordinate followed by the morphism plus the second coordinate followed by the
differential of the target. This is Mathlib's `HomologicalComplex.homotopyCofiber.d_sndX` read
through the data recorded by a cone package. -/
theorem d_coneRetractionX (P : ConePackage f) (n : ℤ) :
    P.cone.complex.d n (n + 1) ≫ P.coneRetractionX (n + 1) =
      ((P.componentIso n).hom ≫ biprod.fst) ≫ f.toHomologicalComplex.f (n + 1) +
        P.coneRetractionX n ≫ L.complex.d n (n + 1) := by
  show P.cone.complex.d n (n + 1) ≫ (P.componentIso (n + 1)).hom ≫ biprod.snd =
    ((P.componentIso n).hom ≫ biprod.fst) ≫ f.toHomologicalComplex.f (n + 1) +
      ((P.componentIso n).hom ≫ biprod.snd) ≫ L.complex.d n (n + 1)
  simp only [Category.assoc]
  rcases P with ⟨Cone, incl, proj, hC, iso, hIso, _, _, _, _⟩
  cases Cone with
  | mk Cx mul assoc one leibniz =>
    dsimp only at hC hIso ⊢
    subst Cx
    have hi : iso = fun n => coneComponentIso f n := by
      funext n
      exact eq_of_heq (hIso n)
    subst iso
    simpa only [coneComponentIso, HomologicalComplex.homotopyCofiber.fstX,
      ← coneSecond_eq, coneSecond, coneComponentIso, Category.assoc] using!
      HomologicalComplex.homotopyCofiber.d_sndX f.toHomologicalComplex n (n + 1) rfl

/-- The differential of a cone in the second coordinate of its degreewise splitting, with the
first coordinate spelled through the cone's projection. -/
theorem d_coneRetractionX_projection (P : ConePackage f) (n : ℤ) :
    P.cone.complex.d n (n + 1) ≫ P.coneRetractionX (n + 1) =
      (P.projection.toHomologicalComplex.f n ≫ ((shiftPackage K).xIso n).hom) ≫
          f.toHomologicalComplex.f (n + 1) +
        P.coneRetractionX n ≫ L.complex.d n (n + 1) := by
  rw [P.d_coneRetractionX n, P.projection_f n]

/-- The section of a cone's projection splits it. -/
theorem coneSectionX_projection (P : ConePackage f) (n : ℤ) :
    P.coneSectionX n ≫ P.projection.toHomologicalComplex.f n = 𝟙 _ := by
  rw [← cancel_mono ((shiftPackage K).xIso n).hom, Category.assoc, P.projection_f n,
    Category.id_comp]
  exact P.coneSectionX_fst n

/-- The inclusion of a cone is split by the second coordinate of the degreewise splitting. -/
theorem inclusion_coneRetractionX (P : ConePackage f) (n : ℤ) :
    P.inclusion.toHomologicalComplex.f n ≫ P.coneRetractionX n = 𝟙 _ := by
  show P.inclusion.toHomologicalComplex.f n ≫ (P.componentIso n).hom ≫ biprod.snd = 𝟙 _
  rw [P.inclusion_f n]
  simp

/-- The inclusion of a cone is annihilated by its projection. -/
theorem inclusion_projection (P : ConePackage f) (n : ℤ) :
    P.inclusion.toHomologicalComplex.f n ≫ P.projection.toHomologicalComplex.f n = 0 := by
  rw [← cancel_mono ((shiftPackage K).xIso n).hom, Category.assoc, P.projection_f n,
    P.inclusion_f n, zero_comp]
  simp

/-- The section of a cone's projection is annihilated by the second coordinate of the degreewise
splitting. -/
theorem coneSectionX_coneRetractionX (P : ConePackage f) (n : ℤ) :
    P.coneSectionX n ≫ P.coneRetractionX n = 0 :=
  P.coneSectionX_snd n

/-- **The two coordinates of the degreewise splitting decompose the identity of the cone.** -/
theorem coneRetractionX_inclusion_add (P : ConePackage f) (n : ℤ) :
    P.coneRetractionX n ≫ P.inclusion.toHomologicalComplex.f n +
        P.projection.toHomologicalComplex.f n ≫ P.coneSectionX n = 𝟙 _ := by
  have h₁ : P.coneRetractionX n ≫ P.inclusion.toHomologicalComplex.f n =
      (P.componentIso n).hom ≫ (biprod.snd ≫ biprod.inr) ≫ (P.componentIso n).inv := by
    rw [P.inclusion_f n]
    simp only [coneRetractionX, Category.assoc]
  have h₂ : P.projection.toHomologicalComplex.f n ≫ P.coneSectionX n =
      (P.componentIso n).hom ≫ (biprod.fst ≫ biprod.inl) ≫ (P.componentIso n).inv := by
    rw [show P.coneSectionX n =
        ((shiftPackage K).xIso n).hom ≫ biprod.inl ≫ (P.componentIso n).inv from rfl,
      ← Category.assoc, P.projection_f n]
    simp only [Category.assoc]
  rw [h₁, h₂, ← Preadditive.comp_add, ← Preadditive.add_comp,
    add_comm (biprod.snd ≫ biprod.inr), biprod.total, Category.id_comp, Iso.hom_inv_id]

/-- **The section of a cone's projection, composed with the cone's differential.** The first
summand lands in the image of the cone's inclusion, the second is the differential of the chosen
shift followed by the section. -/
theorem coneSectionX_d (P : ConePackage f) (n : ℤ) :
    P.coneSectionX n ≫ P.cone.complex.d n (n + 1) =
      (((shiftPackage K).xIso n).hom ≫ f.toHomologicalComplex.f (n + 1)) ≫
          P.inclusion.toHomologicalComplex.f (n + 1) +
        (shift K).complex.d n (n + 1) ≫ P.coneSectionX (n + 1) := by
  have hdr : P.coneSectionX n ≫ P.cone.complex.d n (n + 1) ≫ P.coneRetractionX (n + 1) =
      ((shiftPackage K).xIso n).hom ≫ f.toHomologicalComplex.f (n + 1) := by
    rw [P.d_coneRetractionX n, Preadditive.comp_add,
      ← Category.assoc _ _ (f.toHomologicalComplex.f (n + 1)),
      ← Category.assoc _ _ (L.complex.d n (n + 1)),
      P.coneSectionX_fst n, P.coneSectionX_coneRetractionX n, zero_comp, add_zero]
  have hdp : P.coneSectionX n ≫
      P.cone.complex.d n (n + 1) ≫ P.projection.toHomologicalComplex.f (n + 1) =
        (shift K).complex.d n (n + 1) := by
    rw [← P.projection.toHomologicalComplex.comm n (n + 1), ← Category.assoc,
      P.coneSectionX_projection n, Category.id_comp]
  calc P.coneSectionX n ≫ P.cone.complex.d n (n + 1)
      = P.coneSectionX n ≫ P.cone.complex.d n (n + 1) ≫
          (P.coneRetractionX (n + 1) ≫ P.inclusion.toHomologicalComplex.f (n + 1) +
            P.projection.toHomologicalComplex.f (n + 1) ≫ P.coneSectionX (n + 1)) := by
        rw [P.coneRetractionX_inclusion_add (n + 1), Category.comp_id]
    _ = (P.coneSectionX n ≫ P.cone.complex.d n (n + 1) ≫ P.coneRetractionX (n + 1)) ≫
            P.inclusion.toHomologicalComplex.f (n + 1) +
          (P.coneSectionX n ≫ P.cone.complex.d n (n + 1) ≫
            P.projection.toHomologicalComplex.f (n + 1)) ≫ P.coneSectionX (n + 1) := by
        simp only [Preadditive.comp_add, Category.assoc]
    _ = _ := by rw [hdr, hdp]

/-! ### The two coordinates of the splitting and the right action -/

/-- The second coordinate of the degreewise splitting commutes with the right action. -/
theorem coneRetractionX_action (P : ConePackage f) (n i : ℤ) (U : Cᵒᵖ)
    (x : (P.cone.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U) :
    (P.coneRetractionX (n + i)).val.app U ((P.cone.mul n i).app U x y) =
      (L.mul n i).app U ((P.coneRetractionX n).val.app U x) y :=
  P.action_second n i U x y

/-- The section of a cone's projection commutes with the right action. -/
theorem coneSectionX_action (P : ConePackage f) (n i : ℤ) (U : Cᵒᵖ)
    (x : ((shift K).complex.X n).val.obj U) (y : (A.complex.X i).val.obj U) :
    (P.coneSectionX (n + i)).val.app U (((shift K).mul n i).app U x y) =
      (P.cone.mul n i).app U ((P.coneSectionX n).val.app U x) y :=
  P.sections_ext (n + i) U (P.coneSectionX_action_fst n i U x y)
    (P.coneSectionX_action_snd n i U x y)

/-! ### The morphism from the cone of the identity -/

/-- The functoriality map from the cone of the identity of `K` to the cone of `f`. -/
def fromConeId (Pk : ConePackage f) : (conePackage (𝟙 K)).cone ⟶ Pk.cone :=
  (conePackage (𝟙 K)).map Pk (𝟙 K) f rfl

/-- **The square of the two cones commutes**: the inclusion of `K` into the cone of its identity,
followed by the functoriality map, is `f` followed by the inclusion of `L` into the cone of
`f`. -/
theorem inclusion_fromConeId (Pk : ConePackage f) :
    (conePackage (𝟙 K)).inclusion ≫ Pk.fromConeId = f ≫ Pk.inclusion :=
  (conePackage (𝟙 K)).inclusion_map Pk (𝟙 K) f rfl

/-- The functoriality map is compatible with the projections of the two cones. -/
theorem fromConeId_projection (Pk : ConePackage f) (n : ℤ) :
    Pk.fromConeId.toHomologicalComplex.f n ≫ Pk.projection.toHomologicalComplex.f n =
      (conePackage (𝟙 K)).projection.toHomologicalComplex.f n := by
  rw [← cancel_mono ((shiftPackage K).xIso n).hom, Category.assoc, Pk.projection_f n,
    (conePackage (𝟙 K)).projection_f n, fromConeId, ConePackage.map_f]
  simp

/-- The functoriality map, read in the second coordinate of the two degreewise splittings, is
`f`. -/
theorem fromConeId_coneRetractionX (Pk : ConePackage f) (n : ℤ) :
    Pk.fromConeId.toHomologicalComplex.f n ≫ Pk.coneRetractionX n =
      (conePackage (𝟙 K)).coneRetractionX n ≫ f.toHomologicalComplex.f n := by
  rw [fromConeId, ConePackage.map_f]
  simp [coneRetractionX]

/-- The functoriality map carries the section of the projection of the cone of `𝟙 K` to the
section of the projection of the cone of `f`. -/
theorem coneSectionX_fromConeId (Pk : ConePackage f) (n : ℤ) :
    (conePackage (𝟙 K)).coneSectionX n ≫ Pk.fromConeId.toHomologicalComplex.f n =
      Pk.coneSectionX n := by
  rw [fromConeId, ConePackage.map_f]
  simp [coneSectionX]

/-! ### The descent of a cocone on the span -/

/-- Evaluation of a sum of morphisms of sheaves of modules on a section. -/
private theorem add_val_app' {X Y : SheafOfModules.{m} R} (φ ψ : X ⟶ Y) (U : Cᵒᵖ)
    (z : X.val.obj U) : (φ + ψ).val.app U z = φ.val.app U z + ψ.val.app U z := rfl

/-- **The morphism out of the cone of `f` determined by a cocone on the span.** Given a morphism
`h` out of the cone of `𝟙 K` and a morphism `k` out of `L` which agree on `K`, the degreewise
formula is the projection of the cone followed by the section of the projection of the cone of
`𝟙 K` followed by `h`, plus the second coordinate of the degreewise splitting followed by `k`. -/
def pushoutDesc (Pk : ConePackage f) {T : DifferentialGradedModule.{t, a, m} A}
    (h : (conePackage (𝟙 K)).cone ⟶ T) (k : L ⟶ T)
    (hw : (conePackage (𝟙 K)).inclusion ≫ h = f ≫ k) : Pk.cone ⟶ T where
  toHomologicalComplex :=
    { f := fun n => Pk.projection.toHomologicalComplex.f n ≫
            (conePackage (𝟙 K)).coneSectionX n ≫ h.toHomologicalComplex.f n +
          Pk.coneRetractionX n ≫ k.toHomologicalComplex.f n
      comm' := by
        rintro n n' rfl
        have hsd := (conePackage (𝟙 K)).coneSectionX_d n
        rw [id_f, Category.comp_id] at hsd
        have hwn : (conePackage (𝟙 K)).inclusion.toHomologicalComplex.f (n + 1) ≫
            h.toHomologicalComplex.f (n + 1) =
              f.toHomologicalComplex.f (n + 1) ≫ k.toHomologicalComplex.f (n + 1) :=
          congrArg (fun g : K ⟶ T => g.toHomologicalComplex.f (n + 1)) hw
        have hhc := h.toHomologicalComplex.comm n (n + 1)
        have hkc := k.toHomologicalComplex.comm n (n + 1)
        have hpc := Pk.projection.toHomologicalComplex.comm n (n + 1)
        have hrc := Pk.d_coneRetractionX_projection n
        calc (Pk.projection.toHomologicalComplex.f n ≫
                (conePackage (𝟙 K)).coneSectionX n ≫ h.toHomologicalComplex.f n +
              Pk.coneRetractionX n ≫ k.toHomologicalComplex.f n) ≫ T.complex.d n (n + 1)
            = Pk.projection.toHomologicalComplex.f n ≫ (conePackage (𝟙 K)).coneSectionX n ≫
                  ((conePackage (𝟙 K)).cone.complex.d n (n + 1) ≫
                    h.toHomologicalComplex.f (n + 1)) +
                Pk.coneRetractionX n ≫ L.complex.d n (n + 1) ≫
                  k.toHomologicalComplex.f (n + 1) := by
              simp only [Preadditive.add_comp, Category.assoc, hhc, hkc]
          _ = Pk.projection.toHomologicalComplex.f n ≫
                  ((conePackage (𝟙 K)).coneSectionX n ≫
                    (conePackage (𝟙 K)).cone.complex.d n (n + 1)) ≫
                  h.toHomologicalComplex.f (n + 1) +
                Pk.coneRetractionX n ≫ L.complex.d n (n + 1) ≫
                  k.toHomologicalComplex.f (n + 1) := by
              simp only [Category.assoc]
          _ = Pk.projection.toHomologicalComplex.f n ≫
                  ((shift K).complex.d n (n + 1) ≫ (conePackage (𝟙 K)).coneSectionX (n + 1)) ≫
                  h.toHomologicalComplex.f (n + 1) +
                (Pk.projection.toHomologicalComplex.f n ≫ ((shiftPackage K).xIso n).hom) ≫
                  f.toHomologicalComplex.f (n + 1) ≫ k.toHomologicalComplex.f (n + 1) +
                Pk.coneRetractionX n ≫ L.complex.d n (n + 1) ≫
                  k.toHomologicalComplex.f (n + 1) := by
              rw [hsd]
              simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, hwn]
              abel
          _ = (Pk.projection.toHomologicalComplex.f n ≫ (shift K).complex.d n (n + 1)) ≫
                  (conePackage (𝟙 K)).coneSectionX (n + 1) ≫
                  h.toHomologicalComplex.f (n + 1) +
                ((Pk.projection.toHomologicalComplex.f n ≫ ((shiftPackage K).xIso n).hom) ≫
                    f.toHomologicalComplex.f (n + 1) +
                  Pk.coneRetractionX n ≫ L.complex.d n (n + 1)) ≫
                  k.toHomologicalComplex.f (n + 1) := by
              simp only [Preadditive.add_comp, Category.assoc]
              abel
          _ = (Pk.cone.complex.d n (n + 1) ≫ Pk.projection.toHomologicalComplex.f (n + 1)) ≫
                  (conePackage (𝟙 K)).coneSectionX (n + 1) ≫
                  h.toHomologicalComplex.f (n + 1) +
                (Pk.cone.complex.d n (n + 1) ≫ Pk.coneRetractionX (n + 1)) ≫
                  k.toHomologicalComplex.f (n + 1) := by
              rw [hpc, hrc]
          _ = Pk.cone.complex.d n (n + 1) ≫
                (Pk.projection.toHomologicalComplex.f (n + 1) ≫
                    (conePackage (𝟙 K)).coneSectionX (n + 1) ≫
                    h.toHomologicalComplex.f (n + 1) +
                  Pk.coneRetractionX (n + 1) ≫ k.toHomologicalComplex.f (n + 1)) := by
              simp only [Preadditive.comp_add, Category.assoc] }
  map_mul := by
    intro n i U x y
    change ((Pk.projection.toHomologicalComplex.f (n + i) ≫
          (conePackage (𝟙 K)).coneSectionX (n + i) ≫ h.toHomologicalComplex.f (n + i) +
        Pk.coneRetractionX (n + i) ≫ k.toHomologicalComplex.f (n + i)).val.app U)
          ((Pk.cone.mul n i).app U x y) =
      ((T.mul n i).app U)
        (((Pk.projection.toHomologicalComplex.f n ≫
            (conePackage (𝟙 K)).coneSectionX n ≫ h.toHomologicalComplex.f n +
          Pk.coneRetractionX n ≫ k.toHomologicalComplex.f n).val.app U) x) y
    simp only [add_val_app', comp_val_app']
    rw [Pk.projection.map_mul n i U x y, (conePackage (𝟙 K)).coneSectionX_action n i U _ y,
      h.map_mul, Pk.coneRetractionX_action n i U x y, k.map_mul, ← AddMonoidHom.add_apply,
      ← map_add]

/-- Precomposing the degreewise formula of `pushoutDesc` with a morphism `u` into the cone. -/
private theorem comp_pushoutDesc_f (Pk : ConePackage f) {T : DifferentialGradedModule.{t, a, m} A}
    (h : (conePackage (𝟙 K)).cone ⟶ T) (k : L ⟶ T)
    (hw : (conePackage (𝟙 K)).inclusion ≫ h = f ≫ k) (n : ℤ) {X : SheafOfModules.{m} R}
    (u : X ⟶ Pk.cone.complex.X n) :
    u ≫ (Pk.pushoutDesc h k hw).toHomologicalComplex.f n =
      (u ≫ Pk.projection.toHomologicalComplex.f n) ≫
          ((conePackage (𝟙 K)).coneSectionX n ≫ h.toHomologicalComplex.f n) +
        (u ≫ Pk.coneRetractionX n) ≫ k.toHomologicalComplex.f n := by
  simp only [pushoutDesc, Preadditive.comp_add, Category.assoc]

/-- The descent morphism restricted along the inclusion of `L` into the cone of `f` is `k`. -/
theorem inclusion_pushoutDesc (Pk : ConePackage f) {T : DifferentialGradedModule.{t, a, m} A}
    (h : (conePackage (𝟙 K)).cone ⟶ T) (k : L ⟶ T)
    (hw : (conePackage (𝟙 K)).inclusion ≫ h = f ≫ k) :
    Pk.inclusion ≫ Pk.pushoutDesc h k hw = k := by
  refine Hom.ext fun n => ?_
  rw [comp_f, comp_pushoutDesc_f, Pk.inclusion_projection n, Pk.inclusion_coneRetractionX n,
    zero_comp, Category.id_comp, zero_add]

/-- The descent morphism restricted along the functoriality map from the cone of `𝟙 K` is `h`. -/
theorem fromConeId_pushoutDesc (Pk : ConePackage f) {T : DifferentialGradedModule.{t, a, m} A}
    (h : (conePackage (𝟙 K)).cone ⟶ T) (k : L ⟶ T)
    (hw : (conePackage (𝟙 K)).inclusion ≫ h = f ≫ k) :
    Pk.fromConeId ≫ Pk.pushoutDesc h k hw = h := by
  refine Hom.ext fun n => ?_
  have hwn : (conePackage (𝟙 K)).inclusion.toHomologicalComplex.f n ≫
      h.toHomologicalComplex.f n = f.toHomologicalComplex.f n ≫ k.toHomologicalComplex.f n := by
    rw [← comp_f, ← comp_f, hw]
  rw [comp_f, comp_pushoutDesc_f, Pk.fromConeId_projection n, Pk.fromConeId_coneRetractionX n]
  calc _ = ((conePackage (𝟙 K)).coneRetractionX n ≫
            (conePackage (𝟙 K)).inclusion.toHomologicalComplex.f n +
          (conePackage (𝟙 K)).projection.toHomologicalComplex.f n ≫
            (conePackage (𝟙 K)).coneSectionX n) ≫ h.toHomologicalComplex.f n := by
        rw [Preadditive.add_comp]
        simp only [Category.assoc, hwn]
        abel
    _ = h.toHomologicalComplex.f n := by
        rw [(conePackage (𝟙 K)).coneRetractionX_inclusion_add n, Category.id_comp]

/-- A morphism out of the cone of `f` is determined by its restrictions along the functoriality
map from the cone of `𝟙 K` and along the inclusion of `L`. -/
theorem pushoutDesc_uniq (Pk : ConePackage f) {T : DifferentialGradedModule.{t, a, m} A}
    (h : (conePackage (𝟙 K)).cone ⟶ T) (k : L ⟶ T)
    (hw : (conePackage (𝟙 K)).inclusion ≫ h = f ≫ k) (w : Pk.cone ⟶ T)
    (hl : Pk.fromConeId ≫ w = h) (hr : Pk.inclusion ≫ w = k) : w = Pk.pushoutDesc h k hw := by
  refine Hom.ext fun n => ?_
  have hfm : Pk.fromConeId.toHomologicalComplex.f n ≫ w.toHomologicalComplex.f n =
      h.toHomologicalComplex.f n := by rw [← comp_f, hl]
  have hkm : Pk.inclusion.toHomologicalComplex.f n ≫ w.toHomologicalComplex.f n =
      k.toHomologicalComplex.f n := by rw [← comp_f, hr]
  have hsm : Pk.coneSectionX n ≫ w.toHomologicalComplex.f n =
      (conePackage (𝟙 K)).coneSectionX n ≫ h.toHomologicalComplex.f n := by
    rw [← Pk.coneSectionX_fromConeId n, Category.assoc, hfm]
  have := comp_pushoutDesc_f Pk h k hw n (𝟙 _)
  simp only [Category.id_comp] at this
  rw [this]
  calc w.toHomologicalComplex.f n
      = (Pk.coneRetractionX n ≫ Pk.inclusion.toHomologicalComplex.f n +
          Pk.projection.toHomologicalComplex.f n ≫ Pk.coneSectionX n) ≫
          w.toHomologicalComplex.f n := by
        rw [Pk.coneRetractionX_inclusion_add n, Category.id_comp]
    _ = _ := by
        rw [Preadditive.add_comp]
        simp only [Category.assoc, hkm, hsm]
        exact add_comm _ _

/-! ### The cone of `f` as a pushout -/

/-- **The cone of `f` is a colimit of the span `cone (𝟙 K) ⟵ K ⟶ L`**, whose two legs are the
canonical inclusion of `K` into the cone of its identity and `f`, and whose two inclusions are
the functoriality map and the canonical inclusion of `L` into the cone of `f`. -/
def isColimitPushoutCocone (Pk : ConePackage f) :
    IsColimit (PushoutCocone.mk (f := (conePackage (𝟙 K)).inclusion) (g := f)
      Pk.fromConeId Pk.inclusion Pk.inclusion_fromConeId) :=
  PushoutCocone.IsColimit.mk _ (fun s => Pk.pushoutDesc s.inl s.inr s.condition)
    (fun s => Pk.fromConeId_pushoutDesc s.inl s.inr s.condition)
    (fun s => Pk.inclusion_pushoutDesc s.inl s.inr s.condition)
    (fun s w hl hr => Pk.pushoutDesc_uniq s.inl s.inr s.condition w hl hr)

/-- **The mapping cone of `f : K ⟶ L` is the pushout of the cone on the identity of `K` along
`f`**: the square whose span is the canonical inclusion `K ⟶ cone (𝟙 K)` and `f : K ⟶ L`, and
whose two inclusions into `cone f` are the functoriality map
`SheafOfModules.DifferentialGradedModule.ConePackage.fromConeId` and the canonical inclusion
`L ⟶ cone f`, is a pushout square. -/
theorem isPushout (Pk : ConePackage f) :
    CategoryTheory.IsPushout (conePackage (𝟙 K)).inclusion f Pk.fromConeId Pk.inclusion :=
  IsPushout.of_isColimit Pk.isColimitPushoutCocone

end ConePackage

end SheafOfModules.DifferentialGradedModule

end
