module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.InverseImageSectionsSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantSectionsConnected
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafPushforwardNormal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange

/-!
# Inverse images of sheaves without sections supported off a dense open

Let `Y` be an integral normal scheme, `j : V ⟶ Y` the inclusion of a nonempty open and `H` a sheaf
of `Λ`-modules on `Y_étale` with `j⁻¹ H` locally constant and without sections supported off `V`
(the unit `H ⟶ j_* j⁻¹ H` is a monomorphism). For every morphism `f : X ⟶ Y` such that the
preimage `V_X` of `V` is dense in `X`, the inverse image `f⁻¹ H` has no sections supported off
`V_X` either. No finiteness is asked of `f`: this is the injectivity of the base change map
`f⁻¹ j_* M ⟶ j'_* f'⁻¹ M` on `f⁻¹ H`, by a germ argument instead of Tag 0EYS.

The input is that the vanishing locus of a section `h` of `H` over an étale `W ⟶ Y` is closed
(`Stacks.EtaleCohomology.isClosed_etaleModule_zeroLocus`): at a point `w` of its closure take an
integral open neighbourhood `W₀` of `w` (`Stacks.EtaleCohomology.exists_isIntegral_open_of_etale`);
`W₀ ×_Y V` is connected and dense in `W₀`, `h` vanishes on a nonempty étale `W₀`-scheme, hence
its restriction to `W₀ ×_Y V` is zero (`j⁻¹ H` is locally constant,
`Stacks.EtaleCohomology.eq_zero_of_map_eq_zero_of_isLocallyConstantWith`), hence `h|_{W₀} = 0`.
Then `Stacks.EtaleCohomology.smallEtalePullbackAb_section_eq_zero_of_isClosed` applies to the
underlying abelian sheaf.

## Main results

* `Stacks.EtaleCohomology.isClosed_etaleModule_zeroLocus`.
* `Stacks.EtaleCohomology.mono_etaleModuleInverseImageAdj_unit_app_inverseImage`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasSheafify_over_etaleModules_locallyConstantSections

variable (Λ : Type) [Ring Λ]

/-- Local constancy is invariant under isomorphism of sheaves. -/
theorem isLocallyConstantWith_of_iso {X : Scheme.{u}} (Q : ModuleCat.{u + 1} Λ → Prop)
    {G G' : EtaleModules.{u, 0} Λ X} (e : G ≅ G')
    (hG : Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q G) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q G' := by
  intro U
  obtain ⟨I, V, f, hcov, htriv⟩ := hG U
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e'⟩⟩ := htriv i
  exact ⟨E, hE, ⟨e' ≪≫ (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) (V i)).mapIso e⟩⟩

/-- The unit of `etaleModuleRestrictionDirectImageAdj` is injective over `W` iff the unit of
`etaleModuleInverseImageAdj` is. -/
private theorem injective_restrictionDirectImageAdj_unit_app_iff {Y V : Scheme.{u}} (jV : V ⟶ Y)
    [Etale jV] (H : EtaleModules.{u, 0} Λ Y) (W : Y.Etale) :
    Function.Injective
      (((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ jV).unit.app H).hom.app (op W)) ↔
    Function.Injective
      (((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app H).hom.app (op W)) := by
  have hu := (etaleModuleInverseImageAdj.{u, 0} Λ jV).unit_leftAdjointUniq_hom_app
    (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ jV) H
  let e := ((etaleModuleInverseImageAdj.{u, 0} Λ jV).leftAdjointUniq
    (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ jV)).app H
  have h2 : Function.Bijective
      (((etaleModuleDirectImage.{u, 0} Λ jV).map e.hom).hom.app (op W)) :=
    ConcreteCategory.bijective_of_isIso
      (((sheafToPresheaf _ _).mapIso ((etaleModuleDirectImage.{u, 0} Λ jV).mapIso e)).app
        (op W)).hom
  rw [← hu]
  exact ⟨(h2.1.of_comp_iff _).1, h2.1.comp⟩

/-- **No sections supported off `V`, on sections**: if the unit `H ⟶ j_* j⁻¹ H` of an étale `j` is
a monomorphism, restriction `H(W) ⟶ H(W ×_Y V)` is injective. -/
theorem injective_etaleModuleRestrictionDirectImageAdj_unit_app {Y V : Scheme.{u}} (jV : V ⟶ Y)
    [Etale jV] (H : EtaleModules.{u, 0} Λ Y)
    (hη : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app H)) (W : Y.Etale) :
    Function.Injective
      (((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ jV).unit.app H).hom.app (op W)) := by
  refine (injective_restrictionDirectImageAdj_unit_app_iff Λ jV H W).2 ?_
  rw [← ModuleCat.mono_iff_injective]
  have : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app H).hom :=
    (sheafToPresheaf _ _).map_mono _
  exact (NatTrans.mono_iff_mono_app _).1 inferInstance (op W)

/-- The unit of restriction against direct image along an étale `j`, over an étale `U`, is
restriction along `U ×_Y V ⟶ U`. -/
theorem etaleModuleRestrictionDirectImageAdj_unit_app_hom_app_eq {Y V : Scheme.{u}} (jV : V ⟶ Y)
    [Etale jV] (H : EtaleModules.{u, 0} Λ Y) (U : Y.Etale) :
    H.val.map ((Scheme.Etale.smallEtaleComposeBaseChangeAdj jV).counit.app U).op =
      ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ jV).unit.app H).hom.app (op U) :=
  rfl

/-- A section killed by restriction along `d` is killed by restriction along `b` then `a` whenever
`a ≫ b = c ≫ d`. -/
theorem map_map_eq_zero_of_comp_eq {C : Type*} [Category C] {M : Type*} [Ring M]
    (P : Cᵒᵖ ⥤ ModuleCat M) {A B D E : C} {a : A ⟶ B} {b : B ⟶ E} {c : A ⟶ D} {d : D ⟶ E}
    (hcomm : a ≫ b = c ≫ d) {x : P.obj (op E)} (hx : P.map d.op x = 0) :
    P.map a.op (P.map b.op x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, hcomm, op_comp, P.map_comp,
    ConcreteCategory.comp_apply, hx, map_zero]

/-- Base change along a morphism with dense image of a nonempty étale `Y`-scheme is nonempty. -/
theorem nonempty_smallEtaleBaseChange_obj_left {Y V : Scheme.{u}} (jV : V ⟶ Y)
    (hdense : Dense (Set.range jV)) (T : Y.Etale) [Nonempty T.left] :
    Nonempty ((smallEtaleBaseChange jV).obj T).left := by
  obtain ⟨t₀⟩ := ‹Nonempty T.left›
  have : Etale T.hom := T.prop
  have : UniversallyOpen T.hom := UniversallyOpen.of_flat T.hom
  obtain ⟨x, ⟨t, rfl⟩, ⟨v, hv⟩⟩ := hdense.inter_open_nonempty _ T.hom.isOpenMap.isOpen_range
    ⟨_, t₀, rfl⟩
  exact ⟨(Scheme.Pullback.exists_preimage_pullback (f := T.hom) (g := jV) t v hv.symm).choose⟩

/-- **The vanishing locus of a section is closed** for a sheaf `H` of `Λ`-modules on an integral
normal scheme `Y` with `j⁻¹ H` locally constant and no sections supported off the nonempty open
`j : V ⟶ Y`: the set of points of an étale `W ⟶ Y` near which a section `h` over `W` vanishes is
closed (it is open by definition). -/
theorem isClosed_etaleModule_zeroLocus {Y V : Scheme.{u}} [IsIntegral Y] [IsNormal Y]
    (jV : V ⟶ Y) [IsOpenImmersion jV] [Nonempty V] (Q : ModuleCat.{u + 1} Λ → Prop)
    (H : EtaleModules.{u, 0} Λ Y)
    (hloc : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology Q
      ((etaleModuleInverseImage.{u, 0} Λ jV).obj H))
    (hη : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app H))
    (W : Y.Etale) (h : H.val.obj (op W)) :
    IsClosed {w : W.left | ∃ (W' : Y.Etale) (q : W' ⟶ W), w ∈ Set.range q.left ∧
      H.val.map q.op h = 0} := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have : Etale W.hom := W.prop
  obtain ⟨Z₀, i, hi, hZ₀, hwZ⟩ := exists_isIntegral_open_of_etale (X := Y) W.hom w
  have := hi
  have : Nonempty Z₀ := ⟨hwZ.choose⟩
  let W₀ : Y.Etale := Scheme.Etale.mk (i ≫ W.hom)
  have : Nonempty W₀.left := ‹Nonempty Z₀›
  let r : W₀ ⟶ W := MorphismProperty.Over.homMk i rfl trivial
  obtain ⟨z, ⟨z₀, rfl⟩, W', q, ⟨w', hw'⟩, hq⟩ :=
    mem_closure_iff.1 hw _ i.isOpenEmbedding.isOpen_range hwZ
  have : Etale q.left := Etale.of_comp q.left W.hom
  let W'' : Y.Etale := Scheme.Etale.mk (pullback.fst i q.left ≫ i ≫ W.hom)
  let q₀ : W'' ⟶ W₀ := MorphismProperty.Over.homMk (pullback.fst i q.left) rfl trivial
  let s : W'' ⟶ W' := MorphismProperty.Over.homMk (pullback.snd i q.left) (by
    show pullback.snd i q.left ≫ W'.hom = pullback.fst i q.left ≫ i ≫ W.hom
    rw [← MorphismProperty.Over.w q, ← Category.assoc, ← pullback.condition, Category.assoc])
    trivial
  have hq₀ : q₀ ≫ r = s ≫ q := MorphismProperty.Over.Hom.ext pullback.condition
  let h₀ := H.val.map r.op h
  have h₀W'' : H.val.map q₀.op h₀ = 0 := map_map_eq_zero_of_comp_eq H.val hq₀ hq
  have : Nonempty W''.left :=
    ⟨(Scheme.Pullback.exists_preimage_pullback (f := i) (g := q.left) z₀ w' hw'.symm).choose⟩
  let B := smallEtaleBaseChange jV
  let ε := (Scheme.Etale.smallEtaleComposeBaseChangeAdj jV).counit
  let M' := (etaleModuleRestriction.{u, 0} Λ jV).obj H
  have hM' : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology Q M' :=
    isLocallyConstantWith_of_iso Λ Q ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ jV).app H)
      hloc
  have hdense : Dense (Set.range jV) :=
    jV.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  have : Nonempty (B.obj W'').left := nonempty_smallEtaleBaseChange_obj_left jV hdense W''
  have : ConnectedSpace (B.obj W₀).left := by
    have : IrreducibleSpace (B.obj W₀).left := by
      have : Nonempty ↥(Limits.pullback (i ≫ W.hom) jV) :=
        nonempty_smallEtaleBaseChange_obj_left jV hdense W₀
      exact (pullback.fst (i ≫ W.hom) jV).isOpenEmbedding.irreducibleSpace
    infer_instance
  have hs₀ : M'.val.map (B.map q₀).op (H.val.map (ε.app W₀).op h₀) = 0 := by
    show H.val.map ((Scheme.Etale.smallEtaleCompose jV).map (B.map q₀)).op
      (H.val.map (ε.app W₀).op h₀) = 0
    exact map_map_eq_zero_of_comp_eq H.val (ε.naturality q₀) h₀W''
  exact ⟨W₀, r, hwZ, injective_etaleModuleRestrictionDirectImageAdj_unit_app Λ jV H hη W₀
    ((eq_zero_of_map_eq_zero_of_isLocallyConstantWith Λ Q M' hM' (B.map q₀) _ hs₀).trans
      (map_zero _).symm)⟩

/-- **Converse of `injective_etaleModuleRestrictionDirectImageAdj_unit_app`**: if restriction
`G(U) ⟶ G(U ×_X V)` is injective for every étale `U`, the unit `G ⟶ i_* i⁻¹ G` is a
monomorphism. -/
theorem mono_etaleModuleInverseImageAdj_unit_app_of_injective {X V : Scheme.{u}} (i : V ⟶ X)
    [Etale i] (G : EtaleModules.{u, 0} Λ X)
    (h : ∀ U : X.Etale, Function.Injective
      (((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ i).unit.app G).hom.app (op U))) :
    Mono ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app G) := by
  have hinj : ∀ U : X.Etale, Function.Injective
      (((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app G).hom.app (op U)) := fun U =>
    (injective_restrictionDirectImageAdj_unit_app_iff Λ i G U).1 (h U)
  exact (sheafToPresheaf _ _).mono_of_mono_map ((NatTrans.mono_iff_mono_app _).2 fun U =>
    (ModuleCat.mono_iff_injective _).2 (hinj U.unop))

/-- Under the hypotheses of `mono_etaleModuleInverseImageAdj_unit_app_inverseImage`, restriction of
sections of `f⁻¹ H` along `U ×_X V_X ⟶ U` is injective. -/
theorem injective_etaleModuleRestrictionDirectImageAdj_unit_app_inverseImage {X Y V : Scheme.{u}}
    [IsIntegral Y] [IsNormal Y] (jV : V ⟶ Y) [IsOpenImmersion jV] [Nonempty V]
    (Q : ModuleCat.{u + 1} Λ → Prop) (H : EtaleModules.{u, 0} Λ Y)
    (hloc : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology Q
      ((etaleModuleInverseImage.{u, 0} Λ jV).obj H))
    (hη : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app H))
    (f : X ⟶ Y) (hd : Dense (Set.range (pullback.snd jV f))) (U : X.Etale) :
    Function.Injective
      (((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ (pullback.snd jV f)).unit.app
        ((etaleModuleInverseImage.{u, 0} Λ f).obj H)).hom.app (op U)) := by
  let i := pullback.snd jV f
  let G := (etaleModuleInverseImage.{u, 0} Λ f).obj H
  let F := (etaleModuleForgetAb.{u, 0} Λ Y).obj H
  let Ψ : (smallEtalePullbackAb f).obj F ≅ (etaleModuleForgetAb.{u, 0} Λ X).obj G :=
    (smallEtalePullbackAbConstructionIso f).app F ≪≫ (etaleModuleForgetInverseImageIso Λ f).app H
  let ε := (Scheme.Etale.smallEtaleComposeBaseChangeAdj i).counit
  let G' := (etaleModuleForgetAb.{u, 0} Λ X).obj G
  have hres' : ∀ t : ToType (G'.obj.obj (op U)), G'.obj.map (ε.app U).op t = 0 → t = 0 := by
    intro t ht
    let t' := (Ψ.inv.hom.app (op U)) t
    have hnat : ∀ {U₁ U₂ : X.Etale} (c : U₁ ⟶ U₂) (x : ToType (G'.obj.obj (op U₂))),
        ((smallEtalePullbackAb f).obj F).obj.map c.op (Ψ.inv.hom.app (op U₂) x) =
          Ψ.inv.hom.app (op U₁) (G'.obj.map c.op x) := fun c x =>
      (ConcreteCategory.congr_hom (Ψ.inv.hom.naturality c.op) x).symm
    have ht' : t' = 0 := by
      refine smallEtalePullbackAb_section_eq_zero_of_isClosed f F
        (fun W h => isClosed_etaleModule_zeroLocus Λ jV Q H hloc hη W h)
        ⟨Set.range i, i.isOpenEmbedding.isOpen_range⟩ hd U t' fun U' c hc => ?_
      have : Etale U'.hom := U'.prop
      let ℓ : U'.left ⟶ pullback jV f := IsOpenImmersion.lift i U'.hom hc
      have hℓ : ℓ ≫ i = U'.hom := IsOpenImmersion.lift_fac i U'.hom hc
      have hcU : c.left ≫ U.hom = ℓ ≫ i := (MorphismProperty.Over.w c).trans hℓ.symm
      let c' : U' ⟶ (Scheme.Etale.smallEtaleCompose i).obj ((smallEtaleBaseChange i).obj U) :=
        MorphismProperty.Over.homMk (pullback.lift c.left ℓ hcU) (by
          show pullback.lift c.left ℓ hcU ≫ pullback.snd U.hom i ≫ i = U'.hom
          rw [← Category.assoc, pullback.lift_snd, hℓ]) trivial
      have hfac : c = c' ≫ ε.app U :=
        MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _).symm
      rw [hnat, hfac, op_comp, G'.obj.map_comp, ConcreteCategory.comp_apply, ht, map_zero,
        map_zero]
    have : t = Ψ.hom.hom.app (op U) t' := by
      show t = (Ψ.inv ≫ Ψ.hom).hom.app (op U) t
      rw [Ψ.inv_hom_id]
      rfl
    rw [this, ht', map_zero]
  show Function.Injective (G.val.map (ε.app U).op)
  rw [injective_iff_map_eq_zero]
  exact hres'

/-- **The inverse image of a sheaf without sections supported off a dense open has none off its
preimage.** Let `Y` be integral and normal, `j : V ⟶ Y` a nonempty open, `H` a sheaf of
`Λ`-modules on `Y_étale` with `j⁻¹ H` locally constant and `H ⟶ j_* j⁻¹ H` a monomorphism, and
`f : X ⟶ Y` any morphism such that `V_X = V ×_Y X` is dense in `X`. Then the unit
`f⁻¹ H ⟶ j'_* j'⁻¹ f⁻¹ H` along `j' : V_X ⟶ X` is a monomorphism. -/
theorem mono_etaleModuleInverseImageAdj_unit_app_inverseImage {X Y V : Scheme.{u}}
    [IsIntegral Y] [IsNormal Y] (jV : V ⟶ Y) [IsOpenImmersion jV] [Nonempty V]
    (Q : ModuleCat.{u + 1} Λ → Prop) (H : EtaleModules.{u, 0} Λ Y)
    (hloc : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology Q
      ((etaleModuleInverseImage.{u, 0} Λ jV).obj H))
    (hη : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app H))
    (f : X ⟶ Y) (hd : Dense (Set.range (pullback.snd jV f))) :
    Mono ((etaleModuleInverseImageAdj.{u, 0} Λ (pullback.snd jV f)).unit.app
      ((etaleModuleInverseImage.{u, 0} Λ f).obj H)) :=
  mono_etaleModuleInverseImageAdj_unit_app_of_injective Λ _ _
    (injective_etaleModuleRestrictionDirectImageAdj_unit_app_inverseImage Λ jV Q H hloc hη f hd)

end Stacks.EtaleCohomology

end
