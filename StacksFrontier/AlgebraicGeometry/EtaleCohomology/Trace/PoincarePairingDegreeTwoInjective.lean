module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincarePairingDegreeTwoClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpComplexPrecompQuasiIso

/-!
# A degree-zero cocycle with vanishing `θ` is a boundary

In the base case of the derived Poincaré duality of Tag 03VM, a degree-zero cocycle `β` of
`E = Γ^Gal(X̄_k̄, ℋom^•_ℤ(I, res_ℤ K₀))` acts on the restricted resolutions over a map
`θ_β : res_ℤ((j_! ℱ_M)|) ⟶ res_ℤ((j_! μ_n)|)` (`AlgebraicGeometry.poincareCocycleH0`). This file
proves that `[β] ↦ θ_β` is injective on `H⁰`: if `θ_β = 0` then the class of `β` in `H⁰` of the
underlying complex of `E` vanishes
(`AlgebraicGeometry.homologyπ_eq_zero_of_poincareCocycleH0_eq_zero`).

The argument has three steps.

1. Precomposition with the augmentation `j_! ℱ_M[0] ⟶ I` is a quasi-isomorphism after `Γ^Gal`
   (`Stacks.EtaleCohomology.quasiIso_galoisHomOpE_precomp_injectiveResolution`), so it suffices
   that the image `s` of `β` in `Γ^Gal(ℋom⁰_ℤ(j_! ℱ_M[0], res_ℤ K₀))` is zero.
2. The morphism of `s` (evaluation, `Stacks.EtaleCohomology.sectionPairingAct`) is that of `β`
   precomposed with the augmentation (`Stacks.EtaleCohomology.sectionPairingAct_precomp`), which
   vanishes by `θ_β = 0`.
3. The morphism of a section determines it: `s` comes from a section `c` over a finite stage
   `X̄_E`, every geometric point of `X̄_E` lifts to `X̄_k̄`
   (`Stacks.EtaleCohomology.exists_comp_fieldStageProj_eq`), and the stalk of an inverse image at
   a geometric point is the stalk at its image, so the pairing of `c` with every section vanishes
   (`Stacks.EtaleCohomology.sectionPairing_eq_zero_of_sectionPairingAct_eq_zero`) and `c = 0`.

## Main results

* `Stacks.EtaleCohomology.galoisGlobalSections_map_homOpComplexPrecomp_eq_zero`: steps 2 and 3,
  for any `ι : L' ⟶ L` with `L'` concentrated in degree zero.
* `AlgebraicGeometry.homologyπ_eq_zero_of_poincareCocycleH0_eq_zero`.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe w v u

namespace Stacks.AbelianInternalHom

/-! ### Sections of the internal Hom complex, through evaluation -/

section Eval

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {Λ : Type w} [Ring Λ]
  (L : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ)
  (M : CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ)

/-- **Evaluation after precomposition is evaluation on the image**: `ev(a, e ∘ f) = ev(f a, e)`. -/
lemma homOpEval_homOpComplexPrecompX {L' : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ}
    (f : L' ⟶ L) (n p q : ℤ) (h : p + n = q) (U : Cᵒᵖ) (a : (L'.X n).obj.obj U)
    (e : (homOpComplexX K L M p).obj.obj U) :
    homOpEval K L' M n p q h U a (((homOpComplexPrecompX (M := M) f p).hom.app U).hom e) =
      homOpEval K L M n p q h U (((f.f n).hom.app U).hom a) e := by
  have hπ := congrArg (fun φ : homOpComplexX K L M p ⟶ homOpSheaf K (L'.X n) (M.X q) =>
      ((φ.hom.app U).hom e).app (op (Over.mk (𝟙 U.unop))) a)
    (homOpComplexPrecompX_π K L M f p (⟨(n, q), by omega⟩ : HomOpIndex p))
  exact hπ

/-- **A component of a section vanishes if evaluation against all its restrictions does.** -/
lemma homOpComponent_eq_zero_of_homOpEval (n p q : ℤ) (h : p + n = q) (U : Cᵒᵖ)
    (e : (homOpComplexX K L M p).obj.obj U)
    (hev : ∀ (V : C) (φ : V ⟶ U.unop) (a : (L.X n).obj.obj (op V)),
      homOpEval K L M n p q h (op V) a (((homOpComplexX K L M p).obj.map φ.op).hom e) = 0) :
    homOpComponent K L M n p q h U e = 0 := by
  let η := homOpComponent K L M n p q h U e
  refine NatTrans.ext (funext fun A => ?_)
  let B : Over U.unop := (Over.map A.unop.hom).obj (Over.mk (𝟙 A.unop.left))
  have hB : η.app (op B) = 0 := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
    have h₀ := (homOpEval_apply K L M n p q h _ a _).symm.trans (hev A.unop.left A.unop.hom a)
    exact (congrArg (fun θ : (Over.forget A.unop.left).op ⋙ (toAb K (L.X n)).obj ⟶
        (Over.forget A.unop.left).op ⋙ (M.X q).obj => (θ.app (op (Over.mk (𝟙 A.unop.left)))).hom a)
      (homOpComponent_map K L M n p q h A.unop.hom.op e)).symm.trans h₀
  let ι : op B ≅ A := (Over.isoMk (f := A.unop) (g := B) (Iso.refl _) (by simp [B])).op
  rw [NatTrans.app_zero, ← cancel_epi (((Over.forget U.unop).op ⋙
    (toAb K (L.X n)).obj).map ι.hom), comp_zero, η.naturality, hB, zero_comp]

end Eval

end Stacks.AbelianInternalHom

namespace Stacks.EtaleCohomology

/-! ### Sections vanishing locally -/

section Local

/-- **A section of an étale sheaf of modules which vanishes locally is zero**: if every point of
`V` lies in the image of an étale `U ⟶ V` on which the section restricts to zero. -/
theorem etaleModule_section_eq_zero_of_local {S : Scheme.{u}} {Λ : Type} [Ring Λ]
    (F : EtaleModules.{u, 0} Λ S) {V : S.Etale} (y : F.obj.obj (op V))
    (h : ∀ x : V.left, ∃ (U : S.Etale) (f : U ⟶ V), x ∈ Set.range f.left ∧
      F.obj.map f.op y = 0) :
    y = 0 := by
  choose U f hx hf using h
  have hcov : Sieve.ofArrows U f ∈ smallEtaleTopology S V := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hx x⟩
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose (smallEtaleTopology S) (forget (ModuleCat.{u + 1} Λ))).obj F).property
  refine (hsh.isSeparated _ hcov).ext fun W g hg => ?_
  obtain ⟨x, a, rfl⟩ := Sieve.ofArrows.exists hg
  show F.obj.map (a ≫ f x).op y = F.obj.map (a ≫ f x).op 0
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hf x, map_zero, map_zero]

end Local


/-! ### Sections of the internal Hom complex are determined by their factors -/

section HomOpSections

open Stacks.AbelianInternalHom

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **A section of `ℋom^m_ℤ(L, M)` over `W` whose factors all vanish is zero.** -/
lemma homOpComplexX_section_eq_zero {X : Scheme.{u}} (W : X.Etale) {Λ : Type} [Ring Λ]
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λ)) ℤ)
    (M : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) u}) ℤ) (m : ℤ)
    (e : (homOpComplexX X.smallEtaleTopology L M m).obj.obj (op W))
    (h : ∀ x : HomOpIndex m,
      ((homOpComplexπ X.smallEtaleTopology L M m x).hom.app (op W)).hom e = 0) :
    e = 0 := by
  let E := (sheafSections X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λᵐᵒᵖ)).obj (op W)
  let f := fun x : HomOpIndex m => homOpSheaf X.smallEtaleTopology (L.X x.1.1) (M.X x.1.2)
  have : PreservesLimit (Discrete.functor f) E :=
    preservesLimit_of_natIso _
      (sheafSectionsNatIsoEvaluation X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λᵐᵒᵖ)
        (X := W)).symm
  let φ := piComparison E f ≫
    (ModuleCat.piIsoPi.{0, 0, max (u + 1) u} (fun x => E.obj (f x))).hom
  have hb : Function.Bijective φ := ConcreteCategory.bijective_of_isIso φ
  have key : ∀ (s : E.obj (∏ᶜ f)) (x : HomOpIndex m),
      (φ s : ∀ x, E.obj (f x)) x = (E.map (Pi.π f x)) s := by
    intro s x
    have h1 := ModuleCat.piIsoPi_hom_ker_subtype_apply.{0, 0, max (u + 1) u}
      (fun x => E.obj (f x)) x ((piComparison E f) s)
    simp only at h1
    show ((ModuleCat.piIsoPi.{0, 0, max (u + 1) u} (fun x => E.obj (f x))).hom
      ((piComparison E f) s)) x = _
    rw [h1, ← ConcreteCategory.comp_apply, piComparison_comp_π]
  refine hb.1 (funext fun x => (key e x).trans ((h x).trans ?_))
  exact ((key 0 x).trans (map_zero _)).symm

end HomOpSections

/-! ### The morphism of a section is faithful in the section -/

section Faithful

attribute [local instance] moduleCat_hasLimitsOfSize

variable {Z T : Scheme.{u}} (p : T ⟶ Z) {Λ₁ Λ₂ Λ₃ : Type} [Ring Λ₁] [Ring Λ₂] [Ring Λ₃]
  {G₁ : EtaleModules.{u, 0} Λ₁ Z} {G₂ : EtaleModules.{u, 0} Λ₂ Z} {G₃ : EtaleModules.{u, 0} Λ₃ Z}
  (b : EtaleSectionPairing G₁ G₂ G₃) {W : Z.Etale} {r : T ⟶ W.left} (hr : r ≫ W.hom = p)
  (s : G₂.obj.obj (op W))

/-- The scheme-level identity behind
`Stacks.EtaleCohomology.pointSmallEtale_fiber_map_etaleFiberSection`. -/
lemma comp_smallEtaleBaseChange_map_etaleFiberSection {V : Z.Etale} (φ : V ⟶ W) {A : Scheme.{u}}
    (m : A ⟶ pullback V.hom p)
    (hm : m ≫ pullback.fst V.hom p ≫ φ.left = m ≫ pullback.snd V.hom p ≫ r) :
    m ≫ ((smallEtaleBaseChange p).map (etaleFiberSection W φ)).left =
      m ≫ (etaleFiberLift V p hr).left := by
  have h₁ : ((smallEtaleBaseChange p).map (etaleFiberSection W φ)).left ≫
      pullback.fst (etaleFiberObj V W).hom p =
        pullback.fst V.hom p ≫ pullback.lift (𝟙 V.left) φ.left
          ((Category.id_comp _).trans (MorphismProperty.Over.w φ).symm) :=
    smallEtaleBaseChange_map_left_fst p (etaleFiberSection W φ)
  have h₂ : m ≫ pullback.fst V.hom p ≫ pullback.lift (𝟙 V.left) φ.left
      ((Category.id_comp _).trans (MorphismProperty.Over.w φ).symm) =
        m ≫ pullback.lift (pullback.fst V.hom p) (pullback.snd V.hom p ≫ r)
          (etaleFiberLift_aux V p hr) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst]
      exact congrArg (m ≫ ·) (Category.comp_id (pullback.fst V.hom p))
    · simp only [Category.assoc, pullback.lift_snd]
      exact hm
  refine pullback.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (m ≫ ·) h₁).trans (h₂.trans ?_))
    exact (congrArg (m ≫ ·) (etaleFiberLift_left_fst V p hr)).symm.trans
      (Category.assoc _ _ _).symm
  · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    exact congrArg (m ≫ ·) ((smallEtaleBaseChange_w p _).trans (smallEtaleBaseChange_w p _).symm)

/-- On a geometric point of `V ×_Z T` whose two components agree in `W`, the section `(id, φ)`
of `V ×_Z W` and the lift `(id, r)` define the same geometric point of `(V ×_Z W) ×_Z T`. -/
lemma pointSmallEtale_fiber_map_etaleFiberSection {V : Z.Etale} (φ : V ⟶ W)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] {t : Spec (.of Ω) ⟶ T}
    (g : (pointSmallEtale t).fiber.obj ((smallEtaleBaseChange p).obj V))
    (hg : g.left ≫ pullback.fst V.hom p ≫ φ.left = t ≫ r) :
    (pointSmallEtale t).fiber.map ((smallEtaleBaseChange p).map (etaleFiberSection W φ)) g =
      (pointSmallEtale t).fiber.map (etaleFiberLift V p hr) g := by
  have hgw : g.left ≫ pullback.snd V.hom p = t := Over.w g
  exact Over.OverMorphism.ext (comp_smallEtaleBaseChange_map_etaleFiberSection p hr φ g.left
    (hg.trans ((congrArg (· ≫ r) hgw.symm).trans (Category.assoc _ _ _))))

/-- **The morphism of a section vanishes only if the pairing with it does**: if every geometric
point of `W` lifts along `r : T ⟶ W` and `sectionPairingAct p b hr s = 0`, then `b(a, s|_V) = 0`
for every `V ⟶ W` and every section `a` of `G₁` over `V`. The proof compares stalks: the stalk
of `p⁻¹G₃` at a geometric point of `T` is the stalk of `G₃` at its image. -/
theorem sectionPairing_eq_zero_of_sectionPairingAct_eq_zero
    (hlift : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (w : Spec (.of Ω) ⟶ W.left),
      ∃ t : Spec (.of Ω) ⟶ T, t ≫ r = w)
    (h : sectionPairingAct p b hr s = 0) {V : Z.Etale} (φ : V ⟶ W) (a : G₁.obj.obj (op V)) :
    b.app (op V) a (G₂.obj.map φ.op s) = 0 := by
  refine etaleModule_section_eq_zero_of_local G₃ _ fun x => ?_
  let v := residueGeometricPoint V.left x
  obtain ⟨t, ht⟩ := hlift _ (v ≫ φ.left)
  have hvt : v ≫ V.hom = t ≫ p := by
    rw [← MorphismProperty.Over.w φ, ← Category.assoc, ← ht, Category.assoc, hr]
  let q := pointSmallEtale t
  let u := smallEtaleBaseChange p
  have hu := coverPreserving_smallEtaleBaseChange p
  let g : q.fiber.obj (u.obj V) := Over.homMk (pullback.lift v t hvt) (pullback.lift_snd _ _ _)
  have hgfst : g.left ≫ pullback.fst V.hom p = v := pullback.lift_fst _ _ _
  -- the pairing over `V` is the restriction along `(id, φ)` of the pairing over `V ×_Z W`
  let σ := etaleFiberSection W φ
  let xx := b.app (op (etaleFiberObj V W)) (G₁.obj.map (etaleFiberFst V W).op a)
    (G₂.obj.map (etaleFiberSnd V W).op s)
  have hy : G₃.obj.map σ.op xx = b.app (op V) a (G₂.obj.map φ.op s) := by
    rw [b.naturality σ.op, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      etaleFiberSection_fst, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      etaleFiberSection_snd, op_id, CategoryTheory.Functor.map_id]
    rfl
  let Ψ := q.comap u hu
  let N := (etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃
  -- the germ at the inverse-image point is the germ of the pulled back section
  have hN : N.obj.map (etaleFiberLift V p hr).op (moduleUnitSection Λ₃ p G₃ xx) = 0 := by
    refine (sectionPairingPushforwardFun_apply p b hr s (op V) a).symm.trans ?_
    refine (sectionPairingAct_moduleUnitSection p b hr s a).symm.trans ?_
    rw [h]
    rfl
  have h₁ : q.toPresheafFiber (u.obj (etaleFiberObj V W)) (Ψ.fiber.map σ g) N.obj
      (moduleUnitSection Λ₃ p G₃ xx) = 0 := by
    have hf : Ψ.fiber.map σ g = q.fiber.map (etaleFiberLift V p hr) g :=
      pointSmallEtale_fiber_map_etaleFiberSection p hr φ g
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ.left) hgfst).trans ht.symm))
    have hw := ConcreteCategory.congr_hom (q.toPresheafFiber_w (etaleFiberLift V p hr) g N.obj)
      (moduleUnitSection Λ₃ p G₃ xx)
    rw [ConcreteCategory.comp_apply, hN, map_zero] at hw
    rw [hf]
    exact hw.symm
  have h₂ : Ψ.toPresheafFiber (etaleFiberObj V W) (Ψ.fiber.map σ g) G₃.obj xx = 0 := by
    have hc := ConcreteCategory.congr_hom
      (GrothendieckTopology.Point.toSheafFiber_sheafFiberComapIso_hom
        q u hu G₃ (etaleFiberObj V W) (Ψ.fiber.map σ g)) xx
    rw [ConcreteCategory.comp_apply] at hc
    exact ((ConcreteCategory.isIso_iff_bijective _).1 (inferInstance : IsIso
      ((q.sheafFiberComapIso u hu (ModuleCat.{u + 1} Λ₃)).hom.app G₃))).1
      ((hc.trans h₁).trans (map_zero _).symm)
  have hgerm : Ψ.toPresheafFiber V g G₃.obj (b.app (op V) a (G₂.obj.map φ.op s)) =
      Ψ.toPresheafFiber V g G₃.obj 0 := by
    have hw := ConcreteCategory.congr_hom (Ψ.toPresheafFiber_w (P := G₃.obj) σ g) xx
    rw [ConcreteCategory.comp_apply, hy] at hw
    exact hw.trans (h₂.trans (map_zero _).symm)
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ₃)) := by
    let : PreservesColimitsOfSize.{u + 1, u + 1}
        (forget₂ (ModuleCat.{u + 1} Λ₃) AddCommGrpCat.{u + 1}) :=
      ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ₃
    have : PreservesFilteredColimits (forget (ModuleCat.{u + 1} Λ₃)) :=
      comp_preservesFilteredColimits (forget₂ (ModuleCat.{u + 1} Λ₃) AddCommGrpCat.{u + 1})
        (forget AddCommGrpCat.{u + 1})
    exact preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨U, f, w, hw, hf⟩ := (Ψ.toPresheafFiber_eq_iff' V g _ 0).1 hgerm
  have h₄ : w.left ≫ ((smallEtaleBaseChange p).map f).left = g.left :=
    congrArg (fun k : Over.mk t ⟶ (Etale.forget T).obj (u.obj V) => k.left) hw
  have hw' : w.left ≫ pullback.fst U.hom p ≫ f.left = v :=
    (congrArg (w.left ≫ ·) (smallEtaleBaseChange_map_left_fst p f).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst V.hom p) h₄).trans hgfst))
  refine ⟨U, f, ⟨(w.left ≫ pullback.fst U.hom p)
    (default : Spec (.of (SeparableClosure (V.left.residueField x)))), ?_⟩, hf.trans (map_zero _)⟩
  have h₅ : (w.left ≫ pullback.fst U.hom p) ≫ f.left = v := (Category.assoc _ _ _).trans hw'
  rw [← Scheme.Hom.comp_apply]
  exact (congrArg (fun k : Spec (.of (SeparableClosure (V.left.residueField x))) ⟶ V.left =>
    k default) h₅).trans (residueGeometricPoint_apply V.left x default)

/-- **The morphism is natural in the paired section**: for `v₂ : G₂ ⟶ G₂'` and `v₁ : G₁' ⟶ G₁`
with `b'(a, v₂ c) = b(v₁ a, c)`, the morphism of `v₂ s` through `b'` is `p⁻¹v₁` followed by the
morphism of `s` through `b`. -/
lemma sectionPairingAct_precomp {G₁' : EtaleModules.{u, 0} Λ₁ Z} {G₂' : EtaleModules.{u, 0} Λ₂ Z}
    (b' : EtaleSectionPairing G₁' G₂' G₃) (v₁ : G₁' ⟶ G₁) (v₂ : G₂ ⟶ G₂')
    (hb : ∀ (V : Z.Etale) (a : G₁'.obj.obj (op V)) (c : G₂.obj.obj (op V)),
      b'.app (op V) a (v₂.hom.app (op V) c) = b.app (op V) (v₁.hom.app (op V) a) c) :
    sectionPairingAct p b' hr (v₂.hom.app (op W) s) =
      (etaleModuleRestrictScalars (Int.castRingHom Λ₁) T).map
        ((etaleModuleInverseImage.{u, 0} Λ₁ p).map v₁) ≫ sectionPairingAct p b hr s := by
  refine sectionPairingAct_ext p fun U a => ?_
  show (sectionPairingAct p b' hr (v₂.hom.app (op W) s)).hom.app _
      (moduleUnitSection Λ₁ p G₁' a) =
    (sectionPairingAct p b hr s).hom.app _
      (((etaleModuleInverseImage.{u, 0} Λ₁ p).map v₁).hom.app _ (moduleUnitSection Λ₁ p G₁' a))
  rw [inverseImage_map_moduleUnitSection, sectionPairingAct_moduleUnitSection,
    sectionPairingAct_moduleUnitSection, sectionPairingPushforwardFun_apply,
    sectionPairingPushforwardFun_apply]
  rw [← NatTrans.naturality_apply v₁.hom (etaleFiberFst U W).op a,
    ← NatTrans.naturality_apply v₂.hom (etaleFiberSnd U W).op s, hb]

end Faithful

/-! ### Geometric points of the finite stages lift to `Y_K` -/

section Stage

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u) [Field K] [Algebra k K]
  [Algebra.IsSeparable k K]

/-- **Every geometric point of a finite stage `Y_E` lifts to `Y_K`**: a geometric point
`Spec Ω ⟶ Y_E` gives `E ⟶ Ω`, which extends to `K ⟶ Ω` because `K/E` is separable and `Ω` is
separably closed. -/
theorem exists_comp_fieldStageProj_eq (i : FExt k K) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (w : Spec (.of Ω) ⟶ ((fieldStageSystem Y K).obj (op i)).left) :
    ∃ t : Spec (.of Ω) ⟶ fieldBaseChange Y K, t ≫ fieldStageProj Y K (op i) = w := by
  let a : Spec (.of Ω) ⟶ Spec (.of i.1) := w ≫ pullback.fst (spectrumMap k i.1) Y.hom
  let φ : CommRingCat.of i.1 ⟶ CommRingCat.of Ω := Spec.preimage a
  have ha : Spec.map φ = a := Spec.map_preimage a
  let : Algebra i.1 Ω := φ.hom.toAlgebra
  let ψ : K →ₐ[i.1] Ω := IsSepClosed.lift
  have hψ : CommRingCat.ofHom (algebraMap i.1 K) ≫ CommRingCat.ofHom ψ.toRingHom = φ := by
    ext e
    exact ψ.commutes e
  have h₁ : CommRingCat.ofHom (algebraMap k K) ≫ CommRingCat.ofHom ψ.toRingHom =
      CommRingCat.ofHom (algebraMap k i.1) ≫ φ := by
    ext c
    show ψ (algebraMap k K c) = φ (algebraMap k i.1 c)
    rw [IsScalarTower.algebraMap_apply k i.1 K c]
    exact ψ.commutes _
  have hcond : (w ≫ pullback.snd (spectrumMap k i.1) Y.hom) ≫ Y.hom =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ specAlgebraMap k K := by
    refine (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) pullback.condition.symm).trans
      ((Category.assoc _ _ _).symm.trans ?_))
    show a ≫ Spec.map (CommRingCat.ofHom (algebraMap k i.1)) =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))
    rw [← ha, ← Spec.map_comp, ← Spec.map_comp, h₁]
  refine ⟨pullback.lift (w ≫ pullback.snd (spectrumMap k i.1) Y.hom)
    (Spec.map (CommRingCat.ofHom ψ.toRingHom)) hcond, pullback.hom_ext ?_ ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (fieldStageProj_fst Y K (op i))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pullback.lift_snd _ _ _)).trans
        ((Spec.map_comp _ _).symm.trans ((congrArg Spec.map hψ).trans ha)))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (fieldStageProj_snd Y K (op i))).trans
      (pullback.lift_fst _ _ _))

end Stage

/-! ### A cocycle whose action vanishes on `L'` precomposes to zero -/

section Core

open Stacks.AbelianInternalHom

attribute [local instance] fextOrderBot fextIsDirected etale_spectrumMap_fext

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u) [Field K] [Algebra k K]
  [Algebra.IsSeparable k K] [QuasiCompact Y.hom] [QuasiSeparated Y.hom] {Λ : Type} [Ring Λ]
  {L L' : CochainComplex (EtaleModules.{u, 0} Λ Y.left) ℤ} (ι : L' ⟶ L)
  (Kc : CochainComplex (EtaleModules.{u, 0} ℤ Y.left) ℤ)

/-- **A degree-zero cocycle `β` of `Γ^Gal(ℋom^•_ℤ(L, K))` whose morphism of complexes
`L|_{Y_K} ⟶ K|_{Y_K}` vanishes on `ι : L' ⟶ L` in degree zero precomposes to zero**, when `L'`
is concentrated in degree zero: `Γ^Gal(ι^*)(β) = 0` in `Γ^Gal(ℋom⁰_ℤ(L', K))`.

`β` comes from a section `c` over a finite stage `Y_E`; the morphism of `ι^* c` is that of `c`
precomposed with `ι|`, so it vanishes; geometric points of `Y_E` lift to `Y_K`, so the pairing of
`ι^* c` with every section of `L'⁰` vanishes (stalks); hence `ι^* c = 0`. -/
theorem galoisGlobalSections_map_homOpComplexPrecomp_eq_zero
    (β : ((galoisHomOpE Y K L Kc).X 0).obj.obj.V)
    (hβ : ((galoisHomOpE Y K L Kc).d 0 1).hom.hom.hom.hom β = 0)
    (hL' : ∀ n : ℤ, n ≠ 0 → IsZero (L'.X n))
    (h₀ : (etaleModuleRestrictScalars (Int.castRingHom Λ) (fieldBaseChange Y K)).map
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).map (ι.f 0)) ≫
      (galoisHomOpCocycleAct Y K L Kc β hβ).f 0 = 0) :
    ((galoisGlobalSections Λᵐᵒᵖ Y K).map
      ((homOpComplexPrecomp (M := etaleHomOpTarget Y Kc) ι).f 0)).hom.hom.hom.hom β = 0 := by
  obtain ⟨l, c, hc, -⟩ := exists_fieldStageSection_eq_of_d_eq_zero Y K L Kc β hβ
  let v := (homOpComplexPrecomp (M := etaleHomOpTarget Y Kc) ι).f 0
  let c' := v.hom.app _ c
  let ev := etaleHomOpSectionPairing Y L Kc 0 0 0 (zero_add 0)
  let ev' := etaleHomOpSectionPairing Y L' Kc 0 0 0 (zero_add 0)
  have hact : fieldStageAct Y K ev' l c' = 0 := by
    have e₁ := sectionPairingAct_precomp (fieldBaseChangeProj Y K) ev
      (fieldStageCone_π_comp_hom Y K (op l)) c ev' (ι.f 0) v (fun V a c =>
        homOpEval_homOpComplexPrecompX Y.left.smallEtaleTopology L (etaleHomOpTarget Y Kc) ι
          0 0 0 (zero_add 0) (op V) a c)
    have e₂ : galoisSectionAct Y K ev β = fieldStageAct Y K ev l c := galoisSectionAct_eq Y K ev hc
    exact e₁.trans ((congrArg (_ ≫ ·) e₂.symm).trans h₀)
  have hev : ∀ {V : Y.left.Etale} (φ : V ⟶ (fieldStageSystem Y K).obj (op l))
      (a : (L'.X 0).obj.obj (op V)), ev'.app (op V) a
        ((((etaleHomOpComplex Y L' Kc).X 0).obj.map φ.op).hom c') = 0 :=
    fun φ a => sectionPairing_eq_zero_of_sectionPairingAct_eq_zero (fieldBaseChangeProj Y K) ev'
      (fieldStageCone_π_comp_hom Y K (op l)) c'
      (fun _ _ _ w => exists_comp_fieldStageProj_eq Y K l w) hact φ a
  have hc' : c' = 0 := by
    refine homOpComplexX_section_eq_zero _ L' (etaleHomOpTarget Y Kc) 0 c' fun x => ?_
    obtain ⟨⟨p, q⟩, hpq⟩ := x
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = 0 := by simpa using hpq.symm
      exact homOpComponent_eq_zero_of_homOpEval _ L' (etaleHomOpTarget Y Kc) 0 0 0 (zero_add 0)
        _ c' fun V φ a => hev φ a
    · have hπ := congrArg (fun φ : homOpComplexX Y.left.smallEtaleTopology L
          (etaleHomOpTarget Y Kc) 0 ⟶ homOpSheaf Y.left.smallEtaleTopology (L'.X p)
            ((etaleHomOpTarget Y Kc).X q) => (φ.hom.app _).hom c)
        (homOpComplexPrecompX_π Y.left.smallEtaleTopology L (etaleHomOpTarget Y Kc) ι 0
          ⟨(p, q), hpq⟩)
      rw [(hL' p hp).eq_of_src (ι.f p) 0, homOpMapLeft_zero, comp_zero] at hπ
      exact hπ
  apply ΓRes_etaleMkId_injective
  show ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj Y K)).obj _).ΓRes _
      ((etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ (fieldBaseChange Y K)).map
        ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj Y K)).map v) β) = _
  refine (ΓRes_map_eq_fieldStageSection _ Y K _ v hc).trans ?_
  show fieldStageSection Λᵐᵒᵖ Y K _ l c' = _
  rw [hc', fieldStageSection_zero]
  exact (map_zero _).symm

end Core

/-! ### The augmentation of the restricted resolution in degree zero -/

section Augmentation

variable {Λ : Type} [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {j : CompactificationOf (Over.mk f)}
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar]

/-- The diagram chase behind
`Stacks.EtaleCohomology.singleObjXSelf_inv_comp_compactSupportResolutionIntAugmentation_hom_f`. -/
lemma singleObjXSelf_inv_comp_map_chase {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (r : D ⥤ E) (q : C ⥤ D) {M'' P T G' : C} {M' : D} {M : E} (x : M ≅ r.obj (q.obj G'))
    (y : M' ≅ q.obj G') (g : M'' ≅ G') (u : M'' ⟶ P) (v : P ⟶ M'') (ι : M'' ⟶ T)
    (hu : u ≫ v = 𝟙 M'') :
    x.inv ≫ (x.hom ≫ r.map y.inv) ≫ r.map ((y.hom ≫ q.map g.inv) ≫ q.map u ≫ q.map (v ≫ ι)) =
      r.map (q.map (g.inv ≫ ι)) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, reassoc_of% hu]

omit [Algebra.IsSeparable k kbar] in
/-- **In degree zero, the augmentation `res_ℤ((j_! F)|)[0] ⟶ res_ℤ(I|)` is the restriction of
`j_! F ⟶ I⁰`.** -/
lemma singleObjXSelf_inv_comp_compactSupportResolutionIntAugmentation_hom_f
    (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫
        (compactSupportResolutionIntAugmentation kbar F I).hom.f 0 =
      (etaleModuleRestrictScalars (Int.castRingHom Λ) (fieldBaseChange (Over.mk j.toBase) kbar)).map
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫ I.ι.f 0)) := by
  let r := etaleModuleRestrictScalars (Int.castRingHom Λ) (fieldBaseChange (Over.mk j.toBase) kbar)
  let q := etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  let G := (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F
  let e₃ := mapCochainComplexPlusSinglePlusIso (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) F
  have h₃ : e₃.inv.hom.f 0 ≫ e₃.hom.hom.f 0 = 𝟙 _ :=
    congrArg (fun φ => φ.hom.f 0) e₃.inv_hom_id
  have e₁ : (compactSupportResolutionIntAugmentation kbar F I).hom.f 0 =
      ((HomologicalComplex.singleMapHomologicalComplex r (ComplexShape.up ℤ) 0).inv.app
        (q.obj G)).f 0 ≫
        r.map (((HomologicalComplex.singleMapHomologicalComplex q (ComplexShape.up ℤ) 0).inv.app
          G).f 0 ≫ q.map (e₃.inv.hom.f 0) ≫ q.map (e₃.hom.hom.f 0 ≫ I.ι.f 0)) := rfl
  rw [e₁, HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  exact singleObjXSelf_inv_comp_map_chase r q _ _ _ _ _ _ h₃

end Augmentation

/-! ### Homology classes through a quasi-isomorphism -/

/-- **A cycle mapped to zero by a quasi-isomorphism in its degree has zero homology class.** -/
lemma homologyπ_eq_zero_of_quasiIsoAt {A B : CochainComplex AddCommGrpCat.{w} ℤ} (φ : A ⟶ B)
    (n : ℤ) [QuasiIsoAt φ n] (z : A.cycles n) (hz : (φ.f n).hom ((A.iCycles n).hom z) = 0) :
    (A.homologyπ n).hom z = 0 := by
  have hiso : IsIso (HomologicalComplex.homologyMap φ n) :=
    (quasiIsoAt_iff_isIso_homologyMap φ n).1 inferInstance
  apply (ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap φ n)).1
  have hc : (HomologicalComplex.cyclesMap φ n).hom z = 0 := by
    exact (AddCommGrpCat.mono_iff_injective (B.iCycles n)).1 inferInstance
      ((ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ n) z).trans
        (hz.trans (map_zero _).symm))
  rw [map_zero, ← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, hc, map_zero]

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.GroupCohomology Stacks.EtaleCohomology

/-- The cardinality of a finite ring `Λ` is nonzero. -/
local instance neZero_fintypeCard_bc2Inj (Λ : Type) [Ring Λ] [Fintype Λ] :
    NeZero (Fintype.card Λ) :=
  ⟨Fintype.card_ne_zero⟩

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (Λ : Type) [Ring Λ] [Fintype Λ] [Algebra (ZMod (Fintype.card Λ)) Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod (Fintype.card Λ)) j.immersion).obj
          ((representationSheaf B X _ (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))))))
  [K₀.cocomplex.IsStrictlyGE 0]

/-- **(BC2-inj)** A degree-zero cycle `z` of `Γ^Gal(ℋom^•_ℤ(I, res_ℤ K₀))` whose `θ_z`
(`AlgebraicGeometry.poincareCocycleH0`) vanishes is a boundary. -/
theorem homologyπ_eq_zero_of_poincareCocycleH0_eq_zero
    (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (z : letI := connectedSpace_of_isCurve B X f
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).cycles 0)
    (h : poincareCocycleH0 B X f kbar Λ y j K₀ i _
      (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z) = 0) :
    letI := connectedSpace_of_isCurve B X f
    ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).homologyπ 0).hom z =
      0 := by
  let := connectedSpace_of_isCurve B X f
  have := quasiIso_poincareAugmentationL B X f kbar Λ y j i
  have := quasiIso_poincareAugmentationK B X f kbar Λ y j K₀
  have := isStrictlyGE_galoisBaseChangeComplex_poincare B X f kbar Λ y j i
  have := isStrictlyGE_galoisBaseChangeComplex_cyclotomic B X f kbar Λ y j K₀
  -- `θ_β = 0` says that the morphism of `β` vanishes on the augmentation in degree zero
  have hfac := galoisHomOpCocycleH0_fac (Over.mk j.toBase) kbar i.I.cocomplex
    (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)
    (poincareAugmentationL B X f kbar Λ y j i) (poincareAugmentationK B X f kbar Λ y j K₀) _
    (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z)
  have hθ : galoisHomOpCocycleH0 (Over.mk j.toBase) kbar i.I.cocomplex
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)
      (poincareAugmentationL B X f kbar Λ y j i) (poincareAugmentationK B X f kbar Λ y j K₀) _
      (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z) = 0 := h
  rw [hθ, zero_comp, ← Category.assoc] at hfac
  have hL := singleObjXSelf_inv_comp_compactSupportResolutionIntAugmentation_hom_f kbar
    ((representationSheaf B X _ Λ).obj i.M) i.I
  have h₁ : (etaleModuleRestrictScalars (Int.castRingHom Λ)
        (fieldBaseChange (Over.mk j.toBase) kbar)).map
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫ i.I.ι.f 0)) ≫
      (galoisHomOpCocycleAct (Over.mk j.toBase) kbar i.I.cocomplex
        (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) _
        (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z)).f 0 = 0 := by
    rw [← hL]
    exact hfac.symm
  rw [Functor.map_comp, Functor.map_comp, Category.assoc] at h₁
  have h₀ := (cancel_epi _).1 (h₁.trans comp_zero.symm)
  have hs := galoisGlobalSections_map_homOpComplexPrecomp_eq_zero (Over.mk j.toBase) kbar i.I.ι
    (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) _
    (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z)
    (fun n hn => HomologicalComplex.isZero_single_obj_X _ _ _ _ hn) h₀
  have hn : ((Fintype.card Λ : ℕ) : Λ) = 0 := by
    rw [← map_natCast (algebraMap (ZMod (Fintype.card Λ)) Λ), ZMod.natCast_self, map_zero]
  have := quasiIso_galoisHomOpE_precomp_injectiveResolution Λ hn kbar f j
    ((representationSheaf B X _ Λ).obj i.M) i.I K₀.cocomplex 0
  exact homologyπ_eq_zero_of_quasiIsoAt
    (((Stacks.ContinuousCohomology.forgetAb.{0, u, u + 1} Λᵐᵒᵖ
      (kbar ≃ₐ[k] kbar)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (Stacks.AbelianInternalHom.homOpComplexPrecomp
            (M := etaleHomOpTarget (Over.mk j.toBase)
              (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)) i.I.ι))) 0 z hs

end AlgebraicGeometry

end
