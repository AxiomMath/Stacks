module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.FiniteEtaleCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafForgetAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FreeModuleSheaf
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber

/-!
# The torsor of an extension of the constant sheaf by itself

Let `Λ = ℤ/ℓ` and let `0 → Λ_X --i--> E --ε--> Λ_X → 0` be an extension of sheaves of
`Λ`-modules on the small étale site of a scheme `X`. The sections `p` of `E` with `ε(p) = 1`
form a sheaf of sets `P`, a torsor under `Λ_X` for the translations `p ↦ i(a) + p`; it is finite
locally constant, so it is represented by a finite étale `V ⟶ X`
(`Stacks.EtaleCohomology.exists_isFinite_iso_uliftYoneda_of_isFiniteLocallyConstant`). The
translation by the constant section `1` is an automorphism `τ` of `P` with `τ^ℓ = 1`, and on
the fibre of `P` at a point of the site `τ` acts freely and transitively.

## Main definitions

* `Stacks.EtaleCohomology.ExtensionTorsor.oneSection`: the constant section `1` of `Λ_X` over an
  étale `X`-scheme.
* `Stacks.EtaleCohomology.ExtensionTorsor.torsor`: the sheaf of sets `P = ε⁻¹(1)`.
* `Stacks.EtaleCohomology.ExtensionTorsor.translation`: the translation `τ : P ⟶ P` by `1`.

## Main results

* `Stacks.EtaleCohomology.ExtensionTorsor.isFiniteLocallyConstant_torsor`: `P` is finite locally
  constant.
* `Stacks.EtaleCohomology.ExtensionTorsor.translation_pow_app`: `τ^n` is translation by `n`.
* `Stacks.EtaleCohomology.ExtensionTorsor.translation_pow_self`: `τ^ℓ = 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.ExtensionTorsor

variable {X : Scheme.{u}} (ℓ : ℕ)

/-- The constant sheaf `ℤ/ℓ` of `ℤ/ℓ`-modules on the small étale site of `X`. -/
abbrev unitSheaf : EtaleModules.{u, 0} (ZMod ℓ) X :=
  Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod ℓ) X.smallEtaleTopology

/-- The constant section `1` of `ℤ/ℓ_X` over an étale `X`-scheme `V`. -/
def oneSection (V : X.Etale) : (unitSheaf (X := X) ℓ).obj.obj (op V) :=
  (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
    (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))).app (op V) (ULift.up 1)

/-- The constant section `1` restricts to the constant section `1`. -/
theorem map_oneSection {V W : X.Etale} (f : W ⟶ V) :
    (unitSheaf (X := X) ℓ).obj.map f.op (oneSection ℓ V) = oneSection ℓ W :=
  (NatTrans.naturality_apply (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
    (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))) f.op (ULift.up 1)).symm

variable {ℓ} {E : EtaleModules.{u, 0} (ZMod ℓ) X} (i : unitSheaf ℓ ⟶ E)
  (ε : E ⟶ unitSheaf ℓ) (w : i ≫ ε = 0)

/-- The extension read as a short complex of abelian sheaves. -/
abbrev abelianComplex : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (ShortComplex.mk i ε w).map (etaleModuleUnderlyingAbelian X (ZMod ℓ))

/-- The presheaf map `ℤ ⟶ ℤ/ℓ_X`, `n ↦ n · 1`. -/
def oneMap : (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
    (abelianComplex i ε w).X₃.obj where
  app V := AddCommGrpCat.ofHom ((zmultiplesHom _ (oneSection ℓ V.unop)).comp
    AddEquiv.ulift.toAddMonoidHom)
  naturality {V W} f := by
    ext ⟨n⟩
    change n • oneSection ℓ W.unop = (unitSheaf ℓ).obj.map f (n • oneSection ℓ V.unop)
    rw [map_zsmul]
    exact congrArg (n • ·) (map_oneSection ℓ f.unop).symm

/-- The global section `1` of `ℤ/ℓ_X`, as a morphism from the constant abelian sheaf `ℤ`. -/
def oneHom : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ (abelianComplex i ε w).X₃ :=
  ⟨sheafifyLift X.smallEtaleTopology (oneMap i ε w) (abelianComplex i ε w).X₃.property⟩

/-- The presheaf section underlying `oneHom` is `oneMap`. -/
theorem boundaryPresheafSection_oneHom :
    boundaryPresheafSection (abelianComplex i ε w) (oneHom i ε w) = oneMap i ε w :=
  toSheafify_sheafifyLift _ _ _

/-- **The torsor of the extension**: the sheaf of sets of sections `p` of `E` with `ε(p) = 1`. -/
abbrev torsor : Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  fiberSheaf (abelianComplex i ε w) (oneHom i ε w)

/-- A section `p` of the torsor satisfies `ε(p) = 1`. -/
theorem torsor_spec {V : X.Etale} (p : (torsor i ε w).obj.obj (op V)) :
    ε.hom.app (op V) p.1 = oneSection ℓ V := by
  have h2 : (boundaryPresheafSection (abelianComplex i ε w) (oneHom i ε w)).app (op V)
      (ULift.up 1) = oneSection ℓ V := by
    rw [boundaryPresheafSection_oneHom]
    change (1 : ℤ) • oneSection ℓ V = _
    rw [one_smul]
  exact p.2.trans h2

variable {i ε w} (hS : (ShortComplex.mk i ε w).ShortExact)

include hS in
/-- The underlying short complex of abelian sheaves of a short exact extension is short exact. -/
theorem abelianComplex_shortExact : (abelianComplex i ε w).ShortExact :=
  hS.map_of_exact _

/-- The constant section `1`, as a section of the underlying abelian sheaf. -/
def oneSectionAb (V : X.Etale) :
    ((etaleModuleUnderlyingAbelian X (ZMod ℓ)).obj (unitSheaf ℓ)).obj.obj (op V) :=
  oneSection ℓ V

/-- The constant section `1` of the underlying abelian sheaf restricts to `1`. -/
theorem map_oneSectionAb {V W : X.Etale} (f : W ⟶ V) :
    ((etaleModuleUnderlyingAbelian X (ZMod ℓ)).obj (unitSheaf ℓ)).obj.map f.op
      (oneSectionAb (ℓ := ℓ) V) = oneSectionAb W :=
  map_oneSection ℓ f

/-- `ℓ` times the constant section `1` of `ℤ/ℓ` is zero. -/
theorem nsmul_oneSectionAb_self (V : X.Etale) : ℓ • oneSectionAb (ℓ := ℓ) V = 0 := by
  change ℓ • oneSection ℓ V = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]

/-- The constant sheaf `ℤ/ℓ` of modules underlies the constant abelian sheaf `ℤ/ℓ`. -/
def unitSheafUnderlyingIso : (etaleModuleUnderlyingAbelian X (ZMod ℓ)).obj (unitSheaf ℓ) ≅
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}).obj
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) :=
  (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} (ZMod ℓ) X.smallEtaleTopology).app _

include hS in
/-- **The torsor of the extension is finite locally constant.** -/
theorem isFiniteLocallyConstant_torsor [NeZero ℓ] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant X.smallEtaleTopology (torsor i ε w) :=
  have : Finite ((forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}).obj
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) :=
    inferInstanceAs (Finite (ULift.{u + 1} (ZMod ℓ)))
  isFiniteLocallyConstant_fiberSheaf _ _ (abelianComplex_shortExact hS) _
    (unitSheafUnderlyingIso (ℓ := ℓ))

/-- **The translation of the torsor by the constant section `1`.** -/
def translation : End (torsor i ε w) :=
  End.of <| ObjectProperty.homMk
  { app := fun V => TypeCat.ofHom fun p =>
        fiberSheafAct (abelianComplex i ε w) (oneHom i ε w) (abelianComplex_shortExact hS)
          (oneSectionAb V.unop) p
    naturality := fun {V W} f => by
        ext p
        change fiberSheafAct _ _ (abelianComplex_shortExact hS) (oneSectionAb W.unop)
            ((fiberSheaf (abelianComplex i ε w) (oneHom i ε w)).obj.map f.unop.op p) =
          (fiberSheaf (abelianComplex i ε w) (oneHom i ε w)).obj.map f.unop.op
            (fiberSheafAct _ _ (abelianComplex_shortExact hS) (oneSectionAb V.unop) p)
        rw [fiberSheaf_map_fiberSheafAct _ _ (abelianComplex_shortExact hS) f.unop]
        congr 1
        exact (map_oneSectionAb f.unop).symm }

/-- `τ` acts on sections by translation by `1`. -/
theorem translation_app {V : X.Etale} (p : (torsor i ε w).obj.obj (op V)) :
    (translation hS).asHom.hom.app (op V) p =
      fiberSheafAct (abelianComplex i ε w) (oneHom i ε w) (abelianComplex_shortExact hS)
        (oneSectionAb V) p :=
  rfl

/-- **`τⁿ` is the translation by `n`.** -/
theorem translation_pow_app (n : ℕ) {V : X.Etale} (p : (torsor i ε w).obj.obj (op V)) :
    (translation hS ^ n).asHom.hom.app (op V) p =
      fiberSheafAct (abelianComplex i ε w) (oneHom i ε w) (abelianComplex_shortExact hS)
        (n • oneSectionAb V) p := by
  induction n generalizing p with
  | zero =>
    rw [zero_smul, fiberSheafAct_zero]
    rfl
  | succ n ih =>
    rw [pow_succ, End.mul_asHom]
    change (translation hS ^ n).asHom.hom.app (op V) ((translation hS).asHom.hom.app (op V) p) = _
    rw [ih, translation_app, ← fiberSheafAct_add, succ_nsmul, add_comm]

/-- **`τ^ℓ = 1`.** -/
theorem translation_pow_self : translation hS ^ ℓ = 1 := by
  ext : 1
  apply Sheaf.hom_ext
  ext V p
  change (translation hS ^ ℓ).asHom.hom.app (op V.unop) p = p
  rw [translation_pow_app, nsmul_oneSectionAb_self, fiberSheafAct_zero]

section Fibre

/-- The category of `ℤ/ℓ`-modules in universe `u + 1` has colimits of size `u + 1`. -/
local instance : HasColimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} (ZMod ℓ)) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} (ZMod ℓ)

/-- The category of `ℤ/ℓ`-modules in universe `u + 1` has limits of size `u + 1`. -/
local instance : HasLimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} (ZMod ℓ)) :=
  ModuleCat.instHasLimitsOfSize.{u + 1, u + 1, 0}

/-- The forgetful functor on `ℤ/ℓ`-modules preserves filtered colimits of size `u + 1`. -/
local instance : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
    (forget (ModuleCat.{u + 1, 0} (ZMod ℓ))) :=
  comp_preservesFilteredColimits (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1})
    (forget AddCommGrpCat.{u + 1})

variable (Φ : X.smallEtaleTopology.Point.{u + 1}) [NeZero ℓ]

/-- **The fibre of the constant sheaf `ℤ/ℓ` is `ℤ/ℓ`.** -/
def fiberUnitIso :
    (Φ.presheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).obj (unitSheaf (X := X) ℓ).obj ≅
      ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)) :=
  (asIso ((Φ.presheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).map
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))).symm ≪≫
    CategoryTheory.Sites.constantPresheafFiberIso Φ
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))

omit [NeZero ℓ] in
/-- The fibre of the sheafification map, followed by `fiberUnitIso`, is the identification of the
fibre of the constant presheaf. -/
theorem map_toSheafify_fiberUnitIso_hom :
    (Φ.presheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).map
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
          (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))) ≫ (fiberUnitIso (ℓ := ℓ) Φ).hom =
      (CategoryTheory.Sites.constantPresheafFiberIso Φ
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))).hom :=
  IsIso.hom_inv_id_assoc _ _

omit [NeZero ℓ] in
/-- **The germ of the constant section `1` is `1`** under `fiberUnitIso`. -/
theorem fiberUnitIso_toPresheafFiber_oneSection {V : X.Etale} (y : Φ.fiber.obj V) :
    (fiberUnitIso (ℓ := ℓ) Φ).hom
      (Φ.toPresheafFiber V y (unitSheaf (X := X) ℓ).obj (oneSection ℓ V)) = ULift.up 1 := by
  have h1 : Φ.toPresheafFiber V y (unitSheaf (X := X) ℓ).obj (oneSection ℓ V) =
      Φ.presheafFiber.map (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))))
        (Φ.toPresheafFiber V y ((Functor.const X.Etaleᵒᵖ).obj
          (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) (ULift.up 1)) := by
    rw [oneSection, ← ModuleCat.comp_apply, Φ.toPresheafFiber_naturality]
    rfl
  rw [h1]
  have h2 := congrArg (fun φ => φ (ULift.up 1 : ULift.{u + 1} (ZMod ℓ)))
    (congrArg (fun ψ => Φ.toPresheafFiber V y ((Functor.const X.Etaleᵒᵖ).obj
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) ≫ ψ)
      (map_toSheafify_fiberUnitIso_hom (ℓ := ℓ) Φ))
  exact h2.trans <| ConcreteCategory.congr_hom
    (CategoryTheory.Sites.constantPresheafFiberIso_ι Φ
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))) V y) (ULift.up 1 : ULift.{u + 1} (ZMod ℓ))

/-- Under `fiberUnitIso`, the germ of `m • 1` is `m`. -/
private theorem fiberUnitIso_toPresheafFiber_smul_oneSection {n : ℕ}
    (Ψ : X.smallEtaleTopology.Point.{u + 1}) {V : X.Etale} (y : Ψ.fiber.obj V) (m : ZMod n) :
    (fiberUnitIso (ℓ := n) Ψ).hom
      (Ψ.toPresheafFiber V y (unitSheaf (X := X) n).obj (m • oneSection n V)) = ULift.up m := by
  rw [map_smul, map_smul, fiberUnitIso_toPresheafFiber_oneSection]
  ext
  simp

omit [NeZero ℓ] in
/-- The constant presheaf map sends `m` to `m` times the constant section `1`. -/
theorem toSheafify_app_up (V : X.Etale) (m : ZMod ℓ) :
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))).app (op V) (ULift.up m) =
      m • oneSection ℓ V := by
  have h : (ULift.up m : ULift.{u + 1} (ZMod ℓ)) = m • ULift.up 1 := by
    ext
    simp
  rw [h]
  exact ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
    (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))).app (op V)).hom.map_smul m _

omit [NeZero ℓ] in
/-- The action of `τⁿ` on the fibre of the torsor is the `n`-th iterate of the action of `τ`. -/
theorem presheafFiber_map_pow_apply (n : ℕ)
    (t : (Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj) :
    (Φ.presheafFiber (A := Type (u + 1))).map ((translation hS ^ n).asHom.hom) t =
      ((Φ.presheafFiber (A := Type (u + 1))).map (translation hS).asHom.hom)^[n] t := by
  induction n generalizing t with
  | zero =>
    change (Φ.presheafFiber (A := Type (u + 1))).map (𝟙 _) t = t
    rw [CategoryTheory.Functor.map_id]
    rfl
  | succ n ih =>
    rw [pow_succ, End.mul_asHom]
    change (Φ.presheafFiber (A := Type (u + 1))).map ((translation hS).asHom.hom ≫
      (translation hS ^ n).asHom.hom) t = _
    rw [Functor.map_comp, types_comp_apply, ih, Function.iterate_succ_apply]

/-- **The translation acts transitively on the fibre of the torsor.** -/
theorem exists_iterate_eq (t t' : (Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj) :
    ∃ k : ℕ,
      ((Φ.presheafFiber (A := Type (u + 1))).map (translation hS).asHom.hom)^[k] t = t' := by
  obtain ⟨V, y, p, p', rfl, rfl⟩ :=
    Φ.toPresheafFiber_jointly_surjective₂ (A := Type (u + 1)) (P := (torsor i ε w).obj) t t'
  obtain ⟨a, ha⟩ := (bijective_fiberSheafAct (abelianComplex i ε w) (oneHom i ε w)
    (abelianComplex_shortExact hS) p).2 p'
  let a' : (unitSheaf (X := X) ℓ).obj.obj (op V) := a
  set m : ZMod ℓ :=
    ((fiberUnitIso (ℓ := ℓ) Φ).hom (Φ.toPresheafFiber V y (unitSheaf (X := X) ℓ).obj a')).down
  have hgerm : Φ.toPresheafFiber V y (unitSheaf (X := X) ℓ).obj a' =
      Φ.toPresheafFiber V y (unitSheaf (X := X) ℓ).obj (m • oneSection ℓ V) := by
    apply (ModuleCat.mono_iff_injective (fiberUnitIso (ℓ := ℓ) Φ).hom).1 inferInstance
    rw [fiberUnitIso_toPresheafFiber_smul_oneSection]
  obtain ⟨W, g, z, rfl, hW⟩ := (Φ.toPresheafFiber_eq_iff' V y _ _).1 hgerm
  refine ⟨m.val, ?_⟩
  rw [← presheafFiber_map_pow_apply, ← Φ.toPresheafFiber_w_apply g z,
    ← Φ.toPresheafFiber_w_apply g z, Φ.toPresheafFiber_naturality_apply, ← ha]
  congr 1
  rw [translation_pow_app]
  change _ = (torsor i ε w).obj.map g.op (fiberSheafAct _ _ (abelianComplex_shortExact hS) a p)
  rw [fiberSheaf_map_fiberSheafAct _ _ (abelianComplex_shortExact hS) g]
  congr 1
  change _ = (unitSheaf ℓ).obj.map g.op a'
  rw [hW, map_smul, map_oneSection]
  change ((m.val : ℕ) • oneSection ℓ W) = m • oneSection ℓ W
  rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_zmod_val]

omit [NeZero ℓ] in
/-- **The translation acts freely on the fibre of the torsor**: if `τᵏ` fixes a point of the
fibre then `k = 0` in `ℤ/ℓ`. -/
theorem natCast_eq_zero_of_iterate_eq
    (t : (Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj) (k : ℕ)
    (hk : ((Φ.presheafFiber (A := Type (u + 1))).map (translation hS).asHom.hom)^[k] t = t) :
    (k : ZMod ℓ) = 0 := by
  obtain ⟨V, y, p, rfl⟩ :=
    Φ.toPresheafFiber_jointly_surjective (A := Type (u + 1)) (P := (torsor i ε w).obj) t
  rw [← presheafFiber_map_pow_apply, Φ.toPresheafFiber_naturality_apply] at hk
  obtain ⟨W, g, z, rfl, hW⟩ := (Φ.toPresheafFiber_eq_iff' V y _ _).1 hk
  rw [translation_pow_app] at hW
  change (fiberSheaf (abelianComplex i ε w) (oneHom i ε w)).obj.map g.op
    (fiberSheafAct _ _ (abelianComplex_shortExact hS) (k • oneSectionAb V) p) =
      (fiberSheaf (abelianComplex i ε w) (oneHom i ε w)).obj.map g.op p at hW
  have hmap : (abelianComplex i ε w).X₁.obj.map g.op (oneSectionAb V) = oneSectionAb W :=
    map_oneSectionAb g
  rw [fiberSheaf_map_fiberSheafAct _ _ (abelianComplex_shortExact hS) g, map_nsmul, hmap] at hW
  have h0 : k • oneSectionAb (ℓ := ℓ) W = 0 :=
    (bijective_fiberSheafAct (abelianComplex i ε w) (oneHom i ε w)
      (abelianComplex_shortExact hS)
      ((fiberSheaf (abelianComplex i ε w) (oneHom i ε w)).obj.map g.op p)).1
      (hW.trans (fiberSheafAct_zero _ _ (abelianComplex_shortExact hS) _).symm)
  have h1 : (k : ZMod ℓ) • oneSection ℓ W = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact h0
  have h2 := fiberUnitIso_toPresheafFiber_smul_oneSection Φ z (k : ZMod ℓ)
  rw [h1, map_zero] at h2
  simpa using congrArg ULift.down h2.symm

omit [NeZero ℓ] in
include hS in
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse in
/-- **The fibre of the torsor is nonempty.** -/
theorem nonempty_presheafFiber_torsor :
    Nonempty ((Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj) := by
  obtain ⟨R, hR, hne⟩ := Stacks.Cohomology.Torsors.fiberPseudoTorsor_isTorsor.{u + 1}
    (abelianComplex i ε w) (abelianComplex_shortExact hS)
    (boundaryPresheafSection (abelianComplex i ε w) (oneHom i ε w)) (etaleSiteTerminal X)
  have := Φ.uniqueFiberObj (etaleSiteTerminal X) (etaleSiteTerminalIsTerminal X)
  obtain ⟨V, f, hf, y, -⟩ := Φ.jointly_surjective R hR default
  obtain ⟨p⟩ := hne hf
  exact ⟨Φ.toPresheafFiber V y (torsor i ε w).obj p⟩

end Fibre

end Stacks.EtaleCohomology.ExtensionTorsor

end
