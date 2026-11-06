module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseTrivialConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicIntegralDirectImageCohomology
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.ImageStabilizer
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategoryTransitivity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TransitiveFiberConnected

/-!
# The direct image of the constant sheaf along a finite étale cover is a permutation module

Let `g : V ⟶ X` be a connected finite étale cover of a connected scheme of a big étale site, `ȳ` a
geometric point of `V` and `Y` the geometric fibre of `g` at `x̄ = g(ȳ)`, a transitive
`π₁(X, x̄)`-set in which the stabilizer of `ȳ` is the image of `π₁(V, ȳ)`
(`AlgebraicGeometry.range_etaleFundamentalGroupMap_eq_stabilizer`). Then the lisse sheaf of the
permutation module `ℤ/m[Y]` is the direct image `g_* (ℤ/m)_V`:

`ℱ_{ℤ/m[Y]} ≅ g_* ℱ_{ℤ/m}`.

Both sides are lisse (Tag 095B for the right one), and they corepresent the same functor on finite
`π₁(X, x̄)`-modules `P`:
`Hom(P, ℤ/m[Y]) = Hom_{π₁(V, ȳ)}(P, ℤ/m)` (Frobenius reciprocity), and
`Hom(ℱ_P, g_* ℱ_{ℤ/m}) = Hom(g⁻¹ ℱ_P, ℱ_{ℤ/m}) = Hom(ℱ_{P|π₁(V)}, ℱ_{ℤ/m})` (adjunction and
Tag 0DV6), which is the former by Tag 0DV5 (3).

This is the identification of `φ_* φ^* ℱ_ρ` with a permutation module in the proof of
[Stacks, Tag 03VK].

## Main results

* `Stacks.EtaleCohomology.resTrivialHomEquiv`: Frobenius reciprocity.
* `Stacks.EtaleCohomology.nonempty_lisseEtaleSheaf_comp_etaleModuleInverseImage_iso`: Tag 0DV6
  for lisse sheaves, naturally in the module.
* `Stacks.EtaleCohomology.nonempty_lisseEtaleSheaf_permModule_iso`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
* [Stacks Project, Tag 095B](https://stacks.math.columbia.edu/tag/095B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

/-! ### Frobenius reciprocity -/

section Reciprocity

variable {G H : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H] (m : ℕ) [NeZero m] (φ : H →ₜ* G)
  {Y : Type u} [Fintype Y] [MulAction G Y]
  (hY : ∀ y : Y, IsOpen (MulAction.stabilizer G y : Set G)) {y₀ : Y}
  (hstab : φ.toMonoidHom.range = MulAction.stabilizer G y₀)
  (htrans : ∀ y, ∃ g : G, g • y₀ = y)
  (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G)

include hstab in
/-- A map from the restriction to `H` to the trivial module is invariant under the stabilizer of
`y₀`. -/
theorem apply_rho_eq_of_mem_stabilizer
    (l : (finiteTypeContinuousModuleRes (ZMod m) φ).obj P ⟶ trivialContinuousModule m)
    {s : G} (hs : s ∈ MulAction.stabilizer G y₀) (p : P.obj.obj.obj.V) :
    l.hom.hom.hom.hom.hom ((P.obj.obj.obj.ρ s).asHom.hom p) = l.hom.hom.hom.hom.hom p := by
  rw [← hstab] at hs
  obtain ⟨t, rfl⟩ := hs
  exact ConcreteCategory.congr_hom (l.hom.hom.hom.comm t) p

include hstab htrans in
/-- **Frobenius reciprocity**: `Hom_H(P|_H, ℤ/m) = Hom_G(P, ℤ/m[Y])` when `Y` is transitive and
the stabilizer of `y₀` is the image of `H`. -/
def resTrivialHomEquiv :
    ((finiteTypeContinuousModuleRes (ZMod m) φ).obj P ⟶ trivialContinuousModule m) ≃
      (P ⟶ permModule m PUnit.{u + 2} hY) :=
  let rep : Y → G := fun y => Classical.choose (htrans y)
  have hrep : ∀ y, rep y • y₀ = y := fun y => Classical.choose_spec (htrans y)
  { toFun := fun l => finiteTypeContinuousModuleHomMk m
      { toFun := fun p => ⟨fun y _ =>
          (l.hom.hom.hom.hom.hom ((P.obj.obj.obj.ρ (rep y)⁻¹).asHom.hom p)).down⟩
        map_add' := fun p p' => by
          apply ULift.ext
          funext y a
          exact congrArg ULift.down ((congrArg l.hom.hom.hom.hom.hom (map_add _ p p')).trans
            (map_add _ _ _))
        map_smul' := fun c p => by
          apply ULift.ext
          funext y a
          exact congrArg ULift.down ((congrArg l.hom.hom.hom.hom.hom (map_smul _ c p)).trans
            (map_smul _ c _)) }
      (fun g p => by
        apply ULift.ext
        funext y a
        change (l.hom.hom.hom.hom.hom ((P.obj.obj.obj.ρ (rep y)⁻¹).asHom.hom
            ((P.obj.obj.obj.ρ g).asHom.hom p))).down =
          (l.hom.hom.hom.hom.hom ((P.obj.obj.obj.ρ (rep (g⁻¹ • y))⁻¹).asHom.hom p)).down
        set s := (rep (g⁻¹ • y))⁻¹ * g⁻¹ * rep y with hs_def
        have hs : s ∈ MulAction.stabilizer G y₀ := by
          rw [MulAction.mem_stabilizer_iff, hs_def, mul_smul, mul_smul, hrep]
          exact inv_smul_eq_iff.2 (hrep _).symm
        have key : ∀ (b c : G) (x : P.obj.obj.obj.V),
            (P.obj.obj.obj.ρ (b * c)).asHom.hom x =
              (P.obj.obj.obj.ρ b).asHom.hom ((P.obj.obj.obj.ρ c).asHom.hom x) :=
          fun b c x => congrArg (fun f => f.asHom.hom x) (map_mul P.obj.obj.obj.ρ b c)
        have e₁ : (P.obj.obj.obj.ρ (rep y)⁻¹).asHom.hom ((P.obj.obj.obj.ρ g).asHom.hom p) =
            (P.obj.obj.obj.ρ ((rep y)⁻¹ * g)).asHom.hom p := (key _ _ _).symm
        have e₂ : (P.obj.obj.obj.ρ (rep (g⁻¹ • y))⁻¹).asHom.hom p =
            (P.obj.obj.obj.ρ s).asHom.hom ((P.obj.obj.obj.ρ ((rep y)⁻¹ * g)).asHom.hom p) := by
          rw [← key]
          exact congrArg (fun b => (P.obj.obj.obj.ρ b).asHom.hom p) (by rw [hs_def]; group)
        exact congrArg (fun z => (l.hom.hom.hom.hom.hom z).down) e₁ |>.trans
          ((congrArg ULift.down (apply_rho_eq_of_mem_stabilizer m φ hstab P l hs _)).symm.trans
            (congrArg (fun z => (l.hom.hom.hom.hom.hom z).down) e₂.symm)))
    invFun := fun Θ => finiteTypeContinuousModuleHomMk m
      { toFun := fun p => ⟨(Θ.hom.hom.hom.hom.hom p).down y₀ PUnit.unit⟩
        map_add' := fun p p' => by
          apply ULift.ext
          exact congrArg (fun z : ULift.{u + 1} (Y → PUnit.{u + 2} → ZMod m) =>
            z.down y₀ PUnit.unit) (map_add Θ.hom.hom.hom.hom.hom p p')
        map_smul' := fun c p => by
          apply ULift.ext
          exact congrArg (fun z : ULift.{u + 1} (Y → PUnit.{u + 2} → ZMod m) =>
            z.down y₀ PUnit.unit) (map_smul Θ.hom.hom.hom.hom.hom c p) }
      (fun t p => by
        apply ULift.ext
        change (Θ.hom.hom.hom.hom.hom ((P.obj.obj.obj.ρ (φ t)).asHom.hom p)).down y₀ PUnit.unit =
          (Θ.hom.hom.hom.hom.hom p).down y₀ PUnit.unit
        have ht : φ t ∈ MulAction.stabilizer G y₀ := hstab ▸ ⟨t, rfl⟩
        exact (congrArg (fun z : ULift.{u + 1} (Y → PUnit.{u + 2} → ZMod m) =>
            z.down y₀ PUnit.unit) (ConcreteCategory.congr_hom (Θ.hom.hom.hom.comm (φ t)) p)).trans
          (congrArg (fun y' => (Θ.hom.hom.hom.hom.hom p : ULift.{u + 1}
            (Y → PUnit.{u + 2} → ZMod m)).down y' PUnit.unit)
            (MulAction.mem_stabilizer_iff.1 (Subgroup.inv_mem _ ht))))
    left_inv := by
      intro l
      apply finiteTypeContinuousModule_hom_ext m
      intro p
      apply ULift.ext
      exact congrArg ULift.down (apply_rho_eq_of_mem_stabilizer m φ hstab P l
        (Subgroup.inv_mem _ (show rep y₀ ∈ MulAction.stabilizer G y₀ from hrep y₀)) p)
    right_inv := by
      intro Θ
      apply finiteTypeContinuousModule_hom_ext m
      intro p
      apply ULift.ext
      funext y a
      exact (congrArg (fun z : ULift.{u + 1} (Y → PUnit.{u + 2} → ZMod m) =>
          z.down y₀ PUnit.unit) (ConcreteCategory.congr_hom (Θ.hom.hom.hom.comm (rep y)⁻¹) p)).trans
        (congrArg (fun y' => (Θ.hom.hom.hom.hom.hom p : ULift.{u + 1}
          (Y → PUnit.{u + 2} → ZMod m)).down y' PUnit.unit)
          (by rw [inv_inv, hrep])) }

include hstab htrans in
/-- Frobenius reciprocity is natural in the module. -/
theorem resTrivialHomEquiv_naturality
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G}
    (f : P' ⟶ P)
    (l : (finiteTypeContinuousModuleRes (ZMod m) φ).obj P ⟶ trivialContinuousModule m) :
    resTrivialHomEquiv m φ hY hstab htrans P'
        ((finiteTypeContinuousModuleRes (ZMod m) φ).map f ≫ l) =
      f ≫ resTrivialHomEquiv m φ hY hstab htrans P l := by
  apply finiteTypeContinuousModule_hom_ext m
  intro p
  apply ULift.ext
  funext y a
  exact congrArg (fun z => (l.hom.hom.hom.hom.hom z).down)
    (ConcreteCategory.congr_hom (f.hom.hom.hom.comm _) p)

end Reciprocity

/-! ### Tag 0DV6 for lisse sheaves, naturally in the module -/

section Pullback

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} [ConnectedSpace X.1] [ConnectedSpace Y.1]
  (f : Y ⟶ X) (y : GeometricPoint Y.1) (Λ : Type) [CommRing Λ] [Finite Λ]

/-- **Tag 0DV6 for lisse sheaves, naturally in the module**: `f⁻¹ ℱ_P ≅ ℱ_{P|_{π₁(Y, ȳ)}}`. -/
theorem nonempty_lisseEtaleSheaf_comp_etaleModuleInverseImage_iso :
    Nonempty (lisseEtaleSheaf B X (y.map f.hom) Λ ⋙ etaleModuleInverseImage.{u, 0} Λ f.hom ≅
      finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y) ⋙
        lisseEtaleSheaf B Y y Λ) := by
  obtain ⟨α⟩ :=
    nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso B f Λ y
  let EX := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom) Λ
  let EY := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ
  let pull := etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ
  let res := finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)
  let β : EX.inverse ⋙ pull ≅ res ⋙ EY.inverse :=
    Functor.isoWhiskerLeft EX.inverse
        (pull.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft pull EY.unitIso ≪≫
          (Functor.associator pull EY.functor EY.inverse).symm ≪≫
          Functor.isoWhiskerRight α.symm EY.inverse ≪≫
          Functor.associator EX.functor res EY.inverse) ≪≫
      (Functor.associator EX.inverse EX.functor (res ⋙ EY.inverse)).symm ≪≫
      Functor.isoWhiskerRight EX.counitIso (res ⋙ EY.inverse) ≪≫ Functor.leftUnitor _
  exact ⟨Functor.isoWhiskerLeft EX.inverse
      (Functor.isoWhiskerLeft (ObjectProperty.ι _) (etaleSiteSheafPullbackModuleIso B f Λ).symm) ≪≫
    (Functor.associator EX.inverse pull (ObjectProperty.ι _)).symm ≪≫
    Functor.isoWhiskerRight β (ObjectProperty.ι _)⟩

end Pullback

/-! ### The direct image of the constant sheaf -/

section DirectImage

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **The fibre of a connected finite étale cover is transitive** (the converse of
`AlgebraicGeometry.connectedSpace_left_of_exists_smul_eq`). -/
theorem exists_smul_eq_of_connectedSpace_left {S : Scheme.{u}} [ConnectedSpace S]
    {s : GeometricPoint S} (T : FiniteEtaleOver S) [ConnectedSpace T.left]
    (a b : (finiteEtaleFiberFunctor s).obj T) :
    ∃ σ : EtaleFundamentalGroup S s, σ • a = b := by
  have : PreGaloisCategory.IsConnected T := (isConnected_iff_connectedSpace_left T).2 ‹_›
  let _ : IsGaloisCategory (setValuedFiberFunctor (finiteEtaleFiberFintypeFunctor S s)) :=
    Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor s
  have := Stacks.FundamentalGroup.isPretransitive_fiber_of_isConnected
    (finiteEtaleFiberFintypeFunctor S s) T
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut (finiteEtaleFiberFintypeFunctor S s))
    (show (finiteEtaleFiberFintypeFunctor S s).obj T from a)
    (show (finiteEtaleFiberFintypeFunctor S s).obj T from b)
  exact ⟨autMulEquivEtaleFundamentalGroup S s σ, hσ⟩

variable (B : BigEtaleSite.{u}) {X V : B.Scheme} [ConnectedSpace X.1] [ConnectedSpace V.1]
  (g : V ⟶ X) [IsFinite (B.inclusion.map g)] [Etale (B.inclusion.map g)]
  (y : GeometricPoint V.1) (m : ℕ) [NeZero m] (hg : finiteEtale g.hom)
  [Fintype ((finiteEtaleFiberFunctor (y.map g.hom)).obj (finiteEtaleOverSource hg))]
  (hY : ∀ z : (finiteEtaleFiberFunctor (y.map g.hom)).obj (finiteEtaleOverSource hg),
    IsOpen (MulAction.stabilizer (EtaleFundamentalGroup X.1 (y.map g.hom)) z :
      Set (EtaleFundamentalGroup X.1 (y.map g.hom))))

/-- `ℱ_P ↦ ℱ_P` is fully faithful. -/
def lisseEtaleSheafFullyFaithful (Z : B.Scheme) [ConnectedSpace Z.1] (z : GeometricPoint Z.1)
    (Λ : Type) [CommRing Λ] [Finite Λ] : (lisseEtaleSheaf B Z z Λ).FullyFaithful :=
  ((finiteTypeLocallyConstantModuleSheafEquivalence B Z z Λ).fullyFaithfulInverse.comp
      (ObjectProperty.fullyFaithfulι _)).comp
    (SmallEtale.sheafEquiv B Z.1 Z.2 (ModuleCat.{u + 1} Λ)).fullyFaithfulFunctor

/-- **The lisse sheaf of the permutation module of the fibre of `g` is `g_* ℤ/m`**, for a
connected finite étale cover `g : V ⟶ X` and a geometric point `ȳ` of `V`. -/
theorem nonempty_lisseEtaleSheaf_permModule_iso :
    Nonempty ((lisseEtaleSheaf B X (y.map g.hom) (ZMod m)).obj (permModule m PUnit.{u + 2} hY) ≅
      (etaleModuleDirectImage.{u, 0} (ZMod m) g.hom).obj
        ((lisseEtaleSheaf B V y (ZMod m)).obj (trivialContinuousModule m))) := by
  let Λ := ZMod m
  let EX := finiteTypeLocallyConstantModuleSheafEquivalence B X (y.map g.hom) Λ
  let EV := finiteTypeLocallyConstantModuleSheafEquivalence B V y Λ
  let Λt : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup V.1 y) :=
    trivialContinuousModule m
  let LV := (lisseSheaf B V y Λ).obj Λt
  have hLV : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B V.1 V.2) LV := (EV.inverse.obj Λt).property
  let H := (B.smallPushforward g (ModuleCat.{u + 1} Λ)).obj LV
  have hH := isFiniteTypeLocallyConstant_smallPushforward_of_isFinite_of_etale B g Λ LV hLV
  obtain ⟨Q', ⟨ε⟩⟩ : ∃ Q' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map g.hom)),
      Nonempty ((lisseEtaleSheaf B X (y.map g.hom) Λ).obj Q' ≅
        (etaleModuleDirectImage.{u, 0} Λ g.hom).obj ((lisseEtaleSheaf B V y Λ).obj Λt)) :=
    ⟨EX.functor.obj ⟨H, hH⟩,
      ⟨(SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor.mapIso
        ((ObjectProperty.ι _).mapIso (EX.unitIso.app ⟨H, hH⟩).symm) ≪≫
      (SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B g (ModuleCat.{u + 1} Λ)).app LV⟩⟩
  obtain ⟨α⟩ := nonempty_lisseEtaleSheaf_comp_etaleModuleInverseImage_iso B g y Λ
  let FX := lisseEtaleSheafFullyFaithful B X (y.map g.hom) Λ
  let FV := lisseEtaleSheafFullyFaithful B V y Λ
  let adj := etaleModuleInverseImageAdj.{u, 0} Λ g.hom
  let φ := etaleFundamentalGroupMap g.hom y
  have hstab : φ.toMonoidHom.range = MulAction.stabilizer _ (finiteEtaleOverSourcePoint hg y) :=
    range_etaleFundamentalGroupMap_eq_stabilizer hg y
  have : ConnectedSpace (finiteEtaleOverSource hg).left := inferInstanceAs (ConnectedSpace V.1)
  have htrans : ∀ z, ∃ σ : EtaleFundamentalGroup X.1 (y.map g.hom),
      σ • finiteEtaleOverSourcePoint hg y = z :=
    exists_smul_eq_of_connectedSpace_left _ _
  let R := resTrivialHomEquiv m φ hY hstab htrans
  let Ψ : ∀ Z : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map g.hom)),
      (Z ⟶ Q') ≃ ((finiteTypeContinuousModuleRes Λ φ).obj Z ⟶ Λt) := fun Z =>
    ((((FX.homEquiv).trans ((Iso.refl _).homCongr ε)).trans (adj.homEquiv _ _).symm).trans
      ((α.app Z).homCongr (Iso.refl _))).trans FV.homEquiv.symm
  have hΨ : ∀ {Z Z'} (f : Z' ⟶ Z) (h : Z ⟶ Q'),
      Ψ Z' (f ≫ h) = (finiteTypeContinuousModuleRes Λ φ).map f ≫ Ψ Z h := by
    intro Z Z' f h
    apply FV.map_injective
    simp only [Ψ, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Iso.refl_hom,
      Category.id_comp, Category.comp_id, Functor.FullyFaithful.homEquiv_apply,
      Functor.FullyFaithful.homEquiv_symm_apply, Functor.map_comp,
      Functor.FullyFaithful.map_preimage]
    rw [Category.assoc, Adjunction.homEquiv_naturality_left_symm, ← Category.assoc,
      ← Category.assoc]
    congr 1
    exact (α.inv.naturality f).symm
  have hR : ∀ {Z Z' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map g.hom))} (f : Z' ⟶ Z)
      (l : (finiteTypeContinuousModuleRes Λ φ).obj Z ⟶ Λt),
      R Z' ((finiteTypeContinuousModuleRes Λ φ).map f ≫ l) = f ≫ R Z l :=
    fun f l => resTrivialHomEquiv_naturality m φ hY hstab htrans f l
  clear_value R Ψ
  exact ⟨(lisseEtaleSheaf B X (y.map g.hom) Λ).mapIso (Yoneda.ext _ _
    (fun {Z} h => R Z (Ψ Z h)) (fun {Z} Θ => (Ψ Z).symm ((R Z).symm Θ))
    (fun {Z} h => by simp only [Equiv.symm_apply_apply])
    (fun {Z} Θ => by simp only [Equiv.apply_symm_apply])
    (fun {Z Z'} f h => (congrArg (R Z') (hΨ f h)).trans (hR f (Ψ Z h)))).symm ≪≫ ε⟩

end DirectImage

end Stacks.EtaleCohomology
