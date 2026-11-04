module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# The Rees algebra of an inverse image ideal

Let `f : X ⟶ Y` be a morphism of schemes, `ℐ ⊆ 𝒪_Y` a quasi-coherent sheaf of ideals and
`ℐ𝒪_X = ℐ.comap f` its inverse image ideal sheaf. Pulling local sections back along `f` gives a
morphism of sheaves of `𝒪_Y`-modules `ℐⁿ ⟶ f_*((ℐ𝒪_X)ⁿ)`, compatible with the multiplication and
the unit of the Rees algebras `⨁ₙ ℐⁿ` and `⨁ₙ (ℐ𝒪_X)ⁿ`.

## Main definitions

* `Stacks.Blowup.idealPowerKernelComap`: the morphism `ℐⁿ ⟶ f_*((ℐ𝒪_X)ⁿ)` for `n : ℕ`.
* `Stacks.Blowup.reesPieceComap`: the same for `n : ℤ`, zero in negative degrees, so that it is
  a map of the homogeneous pieces of the two Rees algebras.

## Main results

* `Stacks.Blowup.comap_ambient_quotient_eq_zero`: a section of `𝒪_Y` over `V` lying in `ℐⁿ` on
  every affine open of `V` pulls back to a section of `𝒪_X` over `f⁻¹(V)` killed by the quotient
  by `(ℐ𝒪_X)ⁿ`.
* `Stacks.Blowup.reesPieceAmbient_comap`: on ambient sections the map is `f^♯`.
* `Stacks.Blowup.reesPieceComap_mul` and `Stacks.Blowup.reesPieceComap_one`: the map is
  multiplicative and unital, i.e. it is a morphism of graded algebras over `𝒪_Y`.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Blowup

universe u

/-! ### Restriction and the inverse image on sections -/

/-- Restricting the pullback of a section of `𝒪_Y` over `V` to an affine open `W` lying over an
affine open `V₀ ⊆ V` is the pullback of the restriction, through `Scheme.Hom.appLE`. -/
public theorem appLE_factor {X Y : Scheme.{u}} (f : X ⟶ Y) {V V₀ : Y.Opens} {W : X.Opens}
    (hV₀ : V₀ ≤ V) (hW : W ≤ f ⁻¹ᵁ V₀) (hWV : W ≤ f ⁻¹ᵁ V) :
    f.app V ≫ X.presheaf.map (homOfLE hWV).op =
      Y.presheaf.map (homOfLE hV₀).op ≫ f.appLE V₀ W hW := by
  rw [← Scheme.Hom.appLE, Scheme.Hom.map_appLE]

/-- A section `a` of `𝒪_Y` over `V` whose restriction to every affine open of `V` lies in the
`n`-th power of the ideal is killed, after pullback along `f`, by the quotient map
`𝒪_X ⟶ (ι'_n)_* 𝒪_{V((ℐ𝒪_X)ⁿ)}`. -/
public theorem comap_ambient_quotient_eq_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (n : ℕ) (V : Y.Opens) (a : Γ(Y, V))
    (ha : ∀ (V₀ : Y.affineOpens) (h : V₀.1 ≤ V),
      Y.presheaf.map (homOfLE h).op a ∈ I.ideal V₀ ^ n) :
    (((SheafOfModules.unitToPushforwardObjUnit
      ((I.comap f) ^ n).subschemeι.toRingCatSheafHom).val.app (op (f ⁻¹ᵁ V))).hom
        ((f.app V) a)) = 0 := by
  let J := (I.comap f) ^ n
  let q := SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom
  let Q := (SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
    (SheafOfModules.unit J.subscheme.ringCatSheaf)
  apply TopCat.Presheaf.IsSheaf.section_ext (U := op (f ⁻¹ᵁ V)) Q.isSheaf
  intro z hz
  obtain ⟨-, ⟨V₀, hV₀aff, rfl⟩, hzV₀, hV₀V⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show f.base z ∈ V from hz) V.2
  obtain ⟨-, ⟨W, hWaff, rfl⟩, hzW, hWV₀⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show z ∈ f ⁻¹ᵁ V₀ from hzV₀) (f ⁻¹ᵁ V₀).2
  have hV₀V' : V₀ ≤ V := hV₀V
  have hWV₀' : W ≤ f ⁻¹ᵁ V₀ := hWV₀
  have hWV : W ≤ f ⁻¹ᵁ V := le_trans hWV₀' fun _ hx => hV₀V hx
  refine ⟨W, hWV, hzW, ?_⟩
  show ConcreteCategory.hom (Q.val.map (homOfLE hWV).op)
      ((q.val.app (op (f ⁻¹ᵁ V))).hom ((f.app V) a)) =
    ConcreteCategory.hom (Q.val.map (homOfLE hWV).op) 0
  rw [map_zero, ← PresheafOfModules.naturality_apply q.val (homOfLE hWV).op ((f.app V) a)]
  have hb : ConcreteCategory.hom ((SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE hWV).op)
      ((f.app V) a) = (f.appLE V₀ W hWV₀') (Y.presheaf.map (homOfLE hV₀V').op a) := by
    show X.presheaf.map (homOfLE hWV).op ((f.app V) a) = _
    simpa only [CommRingCat.comp_apply] using
      ConcreteCategory.congr_hom (appLE_factor f hV₀V' hWV₀' hWV) a
  rw [hb]
  show ((I.comap f ^ n).subschemeι.app W).hom _ = 0
  rw [← RingHom.mem_ker,
    Scheme.IdealSheafData.ker_subschemeι_app (I.comap f ^ n) ⟨W, hWaff⟩]
  show _ ∈ ((I.comap f).ideal ⟨W, hWaff⟩) ^ n
  rw [Stacks.IdealSheaf.ideal_comap_appLE I f ⟨V₀, hV₀aff⟩ ⟨W, hWaff⟩ hWV₀', ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (ha ⟨V₀, hV₀aff⟩ hV₀V')

/-! ### The inverse image on a homogeneous piece -/

section Comap

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) (n : ℕ)

/-- The composite `ℐⁿ ⊆ 𝒪_Y ⟶ f_* 𝒪_X ⟶ f_*(𝒪_X/(ℐ𝒪_X)ⁿ)` vanishes. -/
public theorem comap_quotient_eq_zero_hom :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (I ^ n).subschemeι.toRingCatSheafHom) ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      (SheafOfModules.pushforward f.toRingCatSheafHom).map
        (SheafOfModules.unitToPushforwardObjUnit
          ((I.comap f) ^ n).subschemeι.toRingCatSheafHom) = 0 := by
  ext V x
  have ha : ∀ (V₀ : Y.affineOpens) (h : V₀.1 ≤ V.unop),
      Y.presheaf.map (homOfLE h).op (reesPieceAmbient I (n : ℤ) V.unop x) ∈ I.ideal V₀ ^ n := by
    intro V₀ h
    have hmem := reesPieceAmbient_mem_affine I (n : ℤ) (Int.natCast_nonneg n) V₀
      (ConcreteCategory.hom ((reesPiece I (n : ℤ)).val.map (homOfLE h).op) x)
    rw [reesPieceAmbient_restrict I (n : ℤ) V₀.1 V.unop h x] at hmem
    simpa using hmem
  exact comap_ambient_quotient_eq_zero f I n V.unop (reesPieceAmbient I (n : ℤ) V.unop x) ha

/-- The inverse image `ℐⁿ ⟶ f_*((ℐ𝒪_X)ⁿ)` on the degree-`n` piece of the Rees algebra: the lift
of `ℐⁿ ⊆ 𝒪_Y ⟶ f_* 𝒪_X` through the kernel of `f_*(𝒪_X ⟶ (ι'_n)_* 𝒪_{V((ℐ𝒪_X)ⁿ)})`, which is
`f_*((ℐ𝒪_X)ⁿ)` since `f_*` preserves kernels. -/
public def idealPowerKernelComap :
    idealPowerKernel I n ⟶
      (Scheme.Modules.pushforward f).obj (idealPowerKernel (I.comap f) n) :=
  kernel.lift
      ((Scheme.Modules.pushforward f).map
        (SheafOfModules.unitToPushforwardObjUnit
          ((I.comap f) ^ n).subschemeι.toRingCatSheafHom))
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (I ^ n).subschemeι.toRingCatSheafHom) ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
      (comap_quotient_eq_zero_hom f I n) ≫
    (PreservesKernel.iso (Scheme.Modules.pushforward f)
      (SheafOfModules.unitToPushforwardObjUnit
        ((I.comap f) ^ n).subschemeι.toRingCatSheafHom)).inv

/-- Followed by the inclusion `f_*((ℐ𝒪_X)ⁿ) ⊆ f_* 𝒪_X`, the inverse image on the degree-`n`
piece is the inclusion `ℐⁿ ⊆ 𝒪_Y` followed by `f^♯`. -/
public theorem idealPowerKernelComap_ι :
    idealPowerKernelComap f I n ≫
        (Scheme.Modules.pushforward f).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            ((I.comap f) ^ n).subschemeι.toRingCatSheafHom)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (I ^ n).subschemeι.toRingCatSheafHom) ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  have h := PreservesKernel.iso_inv_ι (Scheme.Modules.pushforward f)
    (SheafOfModules.unitToPushforwardObjUnit ((I.comap f) ^ n).subschemeι.toRingCatSheafHom)
  exact (Category.assoc _ _ _).trans
    ((congrArg (kernel.lift _ _ (comap_quotient_eq_zero_hom f I n) ≫ ·) h).trans
      (kernel.lift_ι _ _ _))

/-- On ambient sections, the inverse image on the degree-`n` piece is `f^♯`. -/
public theorem idealPowerKernelAmbient_comap (V : Y.Opens)
    (x : (idealPowerKernel I n).val.obj (op V)) :
    idealPowerKernelAmbient (I.comap f) n (f ⁻¹ᵁ V)
        ((idealPowerKernelComap f I n).val.app (op V) x) =
      (f.app V) (idealPowerKernelAmbient I n V x) :=
  congrArg (fun ψ => ConcreteCategory.hom ((SheafOfModules.Hom.val ψ).app (op V)) x)
    (idealPowerKernelComap_ι f I n)

end Comap

/-! ### The inverse image as a morphism of graded algebras -/

section Graded

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData)

/-- The inverse image `ℐⁿ ⟶ f_*((ℐ𝒪_X)ⁿ)` on the homogeneous pieces of the Rees algebra, for
`n : ℤ`: `idealPowerKernelComap` in degree `n ≥ 0` and zero in negative degrees. -/
public def reesPieceComap (n : ℤ) :
    reesPiece I n ⟶
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj (reesPiece (I.comap f) n) :=
  match n with
  | .ofNat k => idealPowerKernelComap f I k
  | .negSucc _ => 0

/-- On ambient sections the inverse image on a homogeneous piece is `f^♯`. -/
public theorem reesPieceAmbient_comap (n : ℤ) (V : Y.Opens)
    (x : (reesPiece I n).val.obj (op V)) :
    reesPieceAmbient (I.comap f) n (f ⁻¹ᵁ V) ((reesPieceComap f I n).val.app (op V) x) =
      (f.app V) (reesPieceAmbient I n V x) := by
  cases n with
  | ofNat k => exact idealPowerKernelAmbient_comap f I k V x
  | negSucc k =>
      show (0 : Γ(X, f ⁻¹ᵁ V)) = (f.app V) (0 : Γ(Y, V))
      rw [map_zero]

/-- The inverse image `reesPieceComap` is multiplicative: the product of two homogeneous sections
of the Rees algebra of `ℐ` pulls back to the product of their pullbacks. -/
public theorem reesPieceComap_mul (i j : ℤ) (V : Y.Opens)
    (x : (reesPiece I i).val.obj (op V)) (y : (reesPiece I j).val.obj (op V)) :
    (reesPieceComap f I (i + j)).val.app (op V) ((reesMultiplication I i j).app (op V) x y) =
      (reesMultiplication (I.comap f) i j).app (op (f ⁻¹ᵁ V))
        ((reesPieceComap f I i).val.app (op V) x)
        ((reesPieceComap f I j).val.app (op V) y) := by
  rcases i with n | n <;> rcases j with m | m
  · have hij : (0 : ℤ) ≤ Int.ofNat n + Int.ofNat m :=
      Int.add_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg m)
    refine reesPieceAmbient_injective (I.comap f) _ hij (f ⁻¹ᵁ V) ?_
    refine (reesPieceAmbient_comap f I _ V _).trans ?_
    refine Eq.trans
      (congrArg (fun t => ConcreteCategory.hom (f.app V) t)
        (reesMultiplication_ambient I _ _ V x y)) ?_
    refine Eq.trans (map_mul (ConcreteCategory.hom (f.app V)) _ _) ?_
    refine Eq.trans ?_ (reesMultiplication_ambient (I.comap f) _ _ (f ⁻¹ᵁ V) _ _).symm
    exact congrArg₂ (· * ·) (reesPieceAmbient_comap f I _ V x).symm
      (reesPieceAmbient_comap f I _ V y).symm
  all_goals exact (map_zero _).trans rfl

/-- The inverse image `reesPieceComap` is unital: the unit of the Rees algebra of `ℐ` pulls back
to the unit of the Rees algebra of `ℐ𝒪_X`. -/
public theorem reesPieceComap_one (V : Y.Opens) :
    (reesPieceComap f I 0).val.app (op V) ((reesUnit I).eval (op V)) =
      (reesUnit (I.comap f)).eval (op (f ⁻¹ᵁ V)) := by
  refine reesPieceAmbient_injective (I.comap f) 0 le_rfl (f ⁻¹ᵁ V) ?_
  refine (reesPieceAmbient_comap f I 0 V _).trans ?_
  refine Eq.trans (congrArg (fun t => ConcreteCategory.hom (f.app V) t)
    (reesUnit_ambient I (op V))) ?_
  refine Eq.trans (map_one (ConcreteCategory.hom (f.app V))) ?_
  exact (reesUnit_ambient (I.comap f) (op (f ⁻¹ᵁ V))).symm



end Graded

end Stacks.Blowup

end
