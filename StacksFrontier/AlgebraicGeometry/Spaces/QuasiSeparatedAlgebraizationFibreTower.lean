module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic

/-!
# Towers of fibre products over the adic fibres

Let `A` be a ring, `I ⊆ A` an ideal, `S = Spec A` and `S_n = Spec (A / I^{n+1})`. This file
collects the bookkeeping on fibre products over the adic fibres `F_n = F ×_S S_n` used in the
quasi-separated case of Stacks 0GHK
(`StacksFrontier/AlgebraicGeometry/Spaces/MorphismAlgebraizationQuasiSeparated.lean`):

* a family of morphisms `φ_n : F_n ⟶ R` compatible with the transition maps `F_n ⟶ F_{n+1}`
  makes the fibre products `F_n ×_R Q` a cartesian tower over the `F_n`;
* the `n`-th adic fibre of `F ×_S P` is `F_n ×_S P`, so a morphism `u : F_n ⟶ Q` induces a
  morphism `(F ×_S P)_n ⟶ Q ×_S P` which is a base change of `u`.

## Main results

* `AlgebraicGeometry.Space.isPullback_fibreTowerSucc`: the tower `F_n ×_R Q` is cartesian.
* `AlgebraicGeometry.Space.isPullback_adicFibreMap_fst`: the adic fibre of a morphism `G ⟶ F`
  is the base change of the morphism along `F_n ⟶ F`.
* `AlgebraicGeometry.Space.isPullback_adicFibreProdMap`: `(F ×_S P)_n ⟶ Q ×_S P` is the base
  change of `u : F_n ⟶ Q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}
  {F G Q R : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}

/-- Properness is stable under base change, read on a cartesian square of presheaves between
algebraic spaces. -/
theorem isProper_snd_of_isPullback {S : Scheme.{u}} {hS' : B.Contains S}
    {W X Y Z : (BigFppfOver B S hS')ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS' W)
    (hX : IsAlgebraicSpace B S hS' X) (hY : IsAlgebraicSpace B S hS' Y)
    (hZ : IsAlgebraicSpace B S hS' Z) {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : IsProper B S hS' f) : IsProper B S hS' snd :=
  (isProper_isStableUnderBaseChange B S hS').of_isPullback
    (IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS')ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS' F))
      sq : IsPullback
        (ObjectProperty.homMk fst : (⟨W, hW⟩ : AlgebraicSpaces B S hS') ⟶ ⟨X, hX⟩)
        (ObjectProperty.homMk snd : (⟨W, hW⟩ : AlgebraicSpaces B S hS') ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS') ⟶ ⟨Z, hZ⟩)
        (ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS') ⟶ ⟨Z, hZ⟩)) hf

/-- Étaleness is stable under base change, read on a cartesian square of presheaves between
algebraic spaces. -/
theorem isEtale_snd_of_isPullback {S : Scheme.{u}} {hS' : B.Contains S}
    {W X Y Z : (BigFppfOver B S hS')ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS' W)
    (hX : IsAlgebraicSpace B S hS' X) (hY : IsAlgebraicSpace B S hS' Y)
    (hZ : IsAlgebraicSpace B S hS' Z) {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : IsEtale B S hS' f) : IsEtale B S hS' snd :=
  isEtale_of_isPullback B S hS'
    (ObjectProperty.homMk fst : (⟨W, hW⟩ : AlgebraicSpaces B S hS') ⟶ ⟨X, hX⟩)
    (ObjectProperty.homMk snd : (⟨W, hW⟩ : AlgebraicSpaces B S hS') ⟶ ⟨Y, hY⟩)
    (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS') ⟶ ⟨Z, hZ⟩)
    (ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS') ⟶ ⟨Z, hZ⟩)
    (IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS')ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS' F)) sq) hf

/-- Two morphisms into the base agree: the base is the terminal presheaf. -/
theorem eq_of_hom_yoneda_baseObject (a b : F ⟶ yoneda.obj (baseObject A B hS)) : a = b :=
  (isTerminal_yoneda_obj_base B (Spec (.of A)) hS).hom_ext a b

/-! ### Cartesian towers of fibre products -/

section Tower

variable {fF : F ⟶ yoneda.obj (baseObject A B hS)}
  (φ : ∀ n, adicFibre A I B hS hSn fF n ⟶ R)
  (hφ : ∀ n, adicFibreSucc A I B hS hSn fF n ≫ φ (n + 1) = φ n) (q : Q ⟶ R)

/-- The transition `F_n ×_R Q ⟶ F_{n+1} ×_R Q` of the tower of fibre products along a compatible
family `φ_n : F_n ⟶ R`. -/
def fibreTowerSucc (n : ℕ) : pullback (φ n) q ⟶ pullback (φ (n + 1)) q :=
  pullback.lift (pullback.fst _ _ ≫ adicFibreSucc A I B hS hSn fF n) (pullback.snd _ _) (by
    rw [Category.assoc, hφ n, pullback.condition])

/-- The transition of the tower of fibre products lies over the transition of the adic fibres. -/
@[reassoc (attr := simp)]
theorem fibreTowerSucc_fst (n : ℕ) :
    fibreTowerSucc φ hφ q n ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ adicFibreSucc A I B hS hSn fF n :=
  pullback.lift_fst _ _ _

/-- The transition of the tower of fibre products commutes with the projections to `Q`. -/
@[reassoc (attr := simp)]
theorem fibreTowerSucc_snd (n : ℕ) :
    fibreTowerSucc φ hφ q n ≫ pullback.snd _ _ = pullback.snd (φ n) q :=
  pullback.lift_snd _ _ _

/-- **The fibre products `F_n ×_R Q` form a cartesian tower over the `F_n`.** -/
theorem isPullback_fibreTowerSucc (n : ℕ) :
    IsPullback (fibreTowerSucc φ hφ q n) (pullback.fst (φ n) q) (pullback.fst (φ (n + 1)) q)
      (adicFibreSucc A I B hS hSn fF n) := by
  refine IsPullback.of_right ?_ (fibreTowerSucc_fst φ hφ q n)
    (IsPullback.of_hasPullback (φ (n + 1)) q).flip
  rw [fibreTowerSucc_snd, hφ n]
  exact (IsPullback.of_hasPullback (φ n) q).flip

end Tower

/-! ### Adic fibres of fibre products over the base -/

/-- **The adic fibre of a morphism is a base change of it.** For `j : G ⟶ F` over the base, the
square `G_n ⟶ G` over `F_n ⟶ F` is cartesian. -/
theorem isPullback_adicFibreMap_fst {fF : F ⟶ yoneda.obj (baseObject A B hS)} (j : G ⟶ F)
    (n : ℕ) :
    IsPullback (pullback.fst (j ≫ fF) (yoneda.map (adicThickeningMap A I B hS hSn n)))
      (adicFibreMap A I B hS hSn j rfl n) j
      (pullback.fst fF (yoneda.map (adicThickeningMap A I B hS hSn n))) := by
  refine IsPullback.of_bot ?_ (adicFibreMap_fst A I B hS hSn j rfl n).symm
    (IsPullback.of_hasPullback fF _)
  rw [adicFibreMap_snd]
  exact IsPullback.of_hasPullback (j ≫ fF) _

section Product

variable {fF : F ⟶ yoneda.obj (baseObject A B hS)} {fQ : Q ⟶ yoneda.obj (baseObject A B hS)}
  {P : BigFppfOver B (Spec (.of A)) hS} (p : P ⟶ baseObject A B hS)

/-- **The `n`-th adic fibre of `F ×_S P` is `F_n ×_S P`**: the square formed by the adic fibre
`(F ×_S P)_n ⟶ F_n` of the projection and the projections to `P` and to the base is
cartesian. -/
theorem isPullback_adicFibre_pullback (n : ℕ) :
    IsPullback (pullback.fst (pullback.fst fF (yoneda.map p) ≫ fF)
        (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ pullback.snd fF (yoneda.map p))
      (adicFibreMap A I B hS hSn (pullback.fst fF (yoneda.map p)) rfl n) (yoneda.map p)
      (pullback.fst fF (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ fF) :=
  (isPullback_adicFibreMap_fst (hSn := hSn) (pullback.fst fF (yoneda.map p)) n).paste_horiz
    (IsPullback.of_hasPullback fF (yoneda.map p)).flip

/-- The morphism `(F ×_S P)_n ⟶ Q ×_S P` induced by a morphism `u : F_n ⟶ Q`. -/
def adicFibreProdMap (n : ℕ) (u : adicFibre A I B hS hSn fF n ⟶ Q) :
    adicFibre A I B hS hSn (pullback.fst fF (yoneda.map p) ≫ fF) n ⟶
      pullback fQ (yoneda.map p) :=
  pullback.lift (adicFibreMap A I B hS hSn (pullback.fst fF (yoneda.map p)) rfl n ≫ u)
    (pullback.fst _ _ ≫ pullback.snd fF (yoneda.map p)) (eq_of_hom_yoneda_baseObject _ _)

/-- The morphism `(F ×_S P)_n ⟶ Q ×_S P` followed by the projection to `Q`. -/
@[reassoc (attr := simp)]
theorem adicFibreProdMap_fst (n : ℕ) (u : adicFibre A I B hS hSn fF n ⟶ Q) :
    adicFibreProdMap (fQ := fQ) p n u ≫ pullback.fst fQ (yoneda.map p) =
      adicFibreMap A I B hS hSn (pullback.fst fF (yoneda.map p)) rfl n ≫ u :=
  pullback.lift_fst _ _ _

/-- The morphism `(F ×_S P)_n ⟶ Q ×_S P` followed by the projection to `P`. -/
@[reassoc (attr := simp)]
theorem adicFibreProdMap_snd (n : ℕ) (u : adicFibre A I B hS hSn fF n ⟶ Q) :
    adicFibreProdMap (fQ := fQ) p n u ≫ pullback.snd fQ (yoneda.map p) =
      pullback.fst _ _ ≫ pullback.snd fF (yoneda.map p) :=
  pullback.lift_snd _ _ _

/-- **`(F ×_S P)_n ⟶ Q ×_S P` is the base change of `u : F_n ⟶ Q`.** -/
theorem isPullback_adicFibreProdMap (n : ℕ) (u : adicFibre A I B hS hSn fF n ⟶ Q) :
    IsPullback (adicFibreProdMap (fQ := fQ) p n u)
      (adicFibreMap A I B hS hSn (pullback.fst fF (yoneda.map p)) rfl n)
      (pullback.fst fQ (yoneda.map p)) u := by
  refine IsPullback.of_right ?_ (adicFibreProdMap_fst p n u)
    (IsPullback.of_hasPullback fQ (yoneda.map p)).flip
  rw [adicFibreProdMap_snd, eq_of_hom_yoneda_baseObject (u ≫ fQ)
    (pullback.fst fF (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ fF)]
  exact isPullback_adicFibre_pullback p n

/-- The morphisms `(F ×_S P)_n ⟶ Q ×_S P` induced by a family `u_n : F_n ⟶ Q` compatible with
the transition maps are compatible with the transition maps. -/
theorem adicFibreSucc_adicFibreProdMap (u : ∀ n, adicFibre A I B hS hSn fF n ⟶ Q)
    (hu : ∀ n, adicFibreSucc A I B hS hSn fF n ≫ u (n + 1) = u n) (n : ℕ) :
    adicFibreSucc A I B hS hSn (pullback.fst fF (yoneda.map p) ≫ fF) n ≫
        adicFibreProdMap (fQ := fQ) p (n + 1) (u (n + 1)) =
      adicFibreProdMap (fQ := fQ) p n (u n) := by
  apply pullback.hom_ext
  · rw [Category.assoc, adicFibreProdMap_fst, adicFibreProdMap_fst,
      adicFibreSucc_adicFibreMap_assoc, hu n]
  · rw [Category.assoc, adicFibreProdMap_snd, adicFibreProdMap_snd, adicFibreSucc_fst_assoc]

end Product

end AlgebraicGeometry.Space

end
