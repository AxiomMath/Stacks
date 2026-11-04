module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemDirectImage
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemPresentationCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemSetSectionsColimit

/-!
# Direct images of sheaves of sets along a limit: the colimit formula

Let `I` be a directed set, let `g_i : X_i ⟶ S_i` be an inverse system of quasi-compact and
quasi-separated morphisms of schemes with affine transition morphisms on both sides, with limit
`g : X ⟶ S`, and let `(F_i, φ_{i'i})` be a system of sheaves of sets on the `X_i` with
`𝓕 = colim f_i⁻¹F_i`. Then

`g_* 𝓕 = colim_i h_i⁻¹ g_{i, *} F_i`,

for the maps given by the base change maps followed by the maps of the system
(`Stacks.EtaleCohomology.LimitDirectImage.baseChangeProjectionMap`). This is the degree zero case
of [Stacks, Tag 0EYM] for sheaves of sets, the input of the proof of conclusion (1) of
[Stacks, Tag 0EZT].

The proof is the source's: for an object `V₀` of the small étale site of a stage `S_{i₀}` with
quasi-compact and quasi-separated underlying scheme, put `W₀ = V₀ ×_{S_{i₀}} X_{i₀}`, which has
quasi-compact and quasi-separated underlying scheme because `g_{i₀}` is quasi-compact and
quasi-separated. The sections of `h_{k i₀, *} g_{k, *} F_k` over `V₀` are those of
`f_{k i₀, *} F_k` over `W₀`, and the sections of `h_{i₀, *} g_* 𝓕` over `V₀` are those of
`f_{i₀, *} 𝓕` over `W₀`, compatibly with the maps of the two colimits; the colimit on the side of
`X` is the degree zero case of [Stacks, Tag 09YQ] over `W₀`, and an elementwise criterion turns the
colimit on the side of `S` into a colimit of sheaves.

## Main results

* `Stacks.EtaleCohomology.Sets.isSheafPullbackColimitPresentation_of_forall_exists`: a
  compatible family presents a colimit of a system of sheaves of sets on the limit as soon as it
  does so elementwise over the quasi-compact quasi-separated objects of the stages.
* `Stacks.EtaleCohomology.Sets.isSheafPullbackColimitPresentation_projectionMap`: the colimit
  formula `g_* 𝓕 = colim_i h_i⁻¹ g_{i, *} F_i`.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Sets

/-! ### The elementwise criterion -/

section Criterion

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D)

/-- **Every system of sheaves of sets has a colimit presentation on the limit**: sheaves of sets
on the small étale site have coproducts and coequalizers. -/
theorem exists_isSheafPullbackColimitPresentation (F : EtaleSheafSystem D (Type (u + 1))) :
    ∃ (𝓕 : Sheaf (smallEtaleTopology c.pt) (Type (u + 1)))
      (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app i)).obj
        (F.obj i) ⟶ 𝓕),
      F.IsSheafPullbackCocone c ι ∧ F.IsSheafPullbackColimitPresentation c 𝓕 ι := by
  have : HasColimitsOfShape (Discrete Iᵒᵖ) (Sheaf (smallEtaleTopology c.pt) (Type (u + 1))) :=
    Sheaf.instHasColimitsOfShape
  have : HasColimitsOfShape (Discrete (Σ i j : Iᵒᵖ, i ⟶ j))
      (Sheaf (smallEtaleTopology c.pt) (Type (u + 1))) :=
    Sheaf.instHasColimitsOfShape
  have : HasCoequalizers (Sheaf (smallEtaleTopology c.pt) (Type (u + 1))) :=
    Sheaf.instHasColimitsOfShape
  let A : Iᵒᵖ → Sheaf (smallEtaleTopology c.pt) (Type (u + 1)) :=
    fun i => (smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app i)).obj (F.obj i)
  let T : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A j ⟶ A i) := fun {i j} a =>
    F.sheafPullbackDiagramMap c (i := i) (j := j) a
  exact ⟨systemColimit A T, systemColimitι A T, fun a => systemColimitι_compatible A T a,
    isSystemColimit_systemColimit A T⟩

/-- The pushed-forward legs of a family followed by a map are the pushed-forward legs followed by
the direct image of the map. -/
lemma pushforwardLeg_comp (F : EtaleSheafSystem D (Type (u + 1)))
    {𝓖 𝓖' : Sheaf (smallEtaleTopology c.pt) (Type (u + 1))}
    (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app i)).obj
      (F.obj i) ⟶ 𝓖) (κ : 𝓖 ⟶ 𝓖') {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) :
    pushforwardLeg c F (fun i => ι i ≫ κ) a =
      pushforwardLeg c F ι a ≫
        (smallEtalePushforward (X := c.pt) (c.π.app i₀) (Type (u + 1))).map κ := by
  rw [← pushforwardUnit_comp_map c F (fun i => ι i ≫ κ) a, ← pushforwardUnit_comp_map c F ι a,
    Functor.map_comp, Category.assoc]

variable [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
  {c} (hc : IsLimit c) (F : EtaleSheafSystem D (Type (u + 1)))
  {𝓑 : Sheaf (smallEtaleTopology c.pt) (Type (u + 1))}
  (ψ : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app i)).obj
    (F.obj i) ⟶ 𝓑)
  (hψ : F.IsSheafPullbackCocone c ψ)

include hc hψ in
/-- **A compatible family presents the colimit as soon as it does so elementwise on the
quasi-compact quasi-separated objects of the stages.** Let `ψ_i : f_i⁻¹F_i ⟶ 𝓑` be compatible
with the maps of the diagram of a system of sheaves of sets. Suppose that for every object `V₀` of
the small étale site of a stage `X_{i₀}` with quasi-compact and quasi-separated underlying scheme,
every section of `𝓑` over `V₀ ×_{X_{i₀}} X` is the image under a pushed-forward leg of a section
of some `F_k` over `V₀ ×_{X_{i₀}} X_k`, and two sections of `F_k` over `V₀ ×_{X_{i₀}} X_k` with
the same image agree at a later stage. Then `ψ` presents `𝓑 = colim f_i⁻¹F_i`. -/
theorem isSheafPullbackColimitPresentation_of_forall_exists
    (hsurj : ∀ (i₀ : Iᵒᵖ) (V₀ : (D.obj i₀).Etale) [CompactSpace V₀.left]
      [QuasiSeparatedSpace V₀.left]
      (s : 𝓑.obj.obj (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀))),
      ∃ (k : Iᵒᵖ) (a : k ⟶ i₀)
        (x : (F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀))),
        (pushforwardLeg c F ψ a).hom.app (op V₀) x = s)
    (hinj : ∀ (i₀ : Iᵒᵖ) (V₀ : (D.obj i₀).Etale) [CompactSpace V₀.left]
      [QuasiSeparatedSpace V₀.left] {k : Iᵒᵖ} (a : k ⟶ i₀)
      (x x' : (F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀))),
      (pushforwardLeg c F ψ a).hom.app (op V₀) x = (pushforwardLeg c F ψ a).hom.app (op V₀) x' →
      ∃ (l : Iᵒᵖ) (b : l ⟶ k), (pushforwardTransition F b a).hom.app (op V₀) x =
        (pushforwardTransition F b a).hom.app (op V₀) x') :
    F.IsSheafPullbackColimitPresentation c 𝓑 ψ := by
  obtain ⟨C, ιC, hιC, hC⟩ := exists_isSheafPullbackColimitPresentation c F
  let κ : C ⟶ 𝓑 := hC.desc ψ hψ
  have hκ : ∀ i, ιC i ≫ κ = ψ i := hC.fac ψ hψ
  have hleg : ∀ {k i₀ : Iᵒᵖ} (a : k ⟶ i₀),
      pushforwardLeg c F ψ a =
        pushforwardLeg c F ιC a ≫
          (smallEtalePushforward (X := c.pt) (c.π.app i₀) (Type (u + 1))).map κ := by
    intro k i₀ a
    rw [← pushforwardLeg_comp c F ιC κ a]
    congr 1
    exact funext fun i => (hκ i).symm
  have happ : ∀ {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) (V₀ : (D.obj i₀).Etale)
      (x : (F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀))),
      κ.hom.app _ ((pushforwardLeg c F ιC a).hom.app (op V₀) x) =
        (pushforwardLeg c F ψ a).hom.app (op V₀) x := fun a V₀ x =>
    (congrArg (fun φ => φ.hom.app (op V₀) x) (hleg a)).symm
  -- two sections of the colimit come from a common stage
  have hcommon : ∀ (i₀ : Iᵒᵖ) (V₀ : (D.obj i₀).Etale) [CompactSpace V₀.left]
      [QuasiSeparatedSpace V₀.left]
      (y y' : C.obj.obj (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀))),
      ∃ (m : Iᵒᵖ) (a : m ⟶ i₀)
        (x x' : (F.obj m).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀))),
        (pushforwardLeg c F ιC a).hom.app (op V₀) x = y ∧
          (pushforwardLeg c F ιC a).hom.app (op V₀) x' = y' := by
    intro i₀ V₀ _ _ y y'
    obtain ⟨k, a, x₀, hx₀⟩ := exists_pushforwardLeg_apply_eq c hc F ιC hιC hC V₀ y
    obtain ⟨k', a', x₀', hx₀'⟩ := exists_pushforwardLeg_apply_eq c hc F ιC hιC hC V₀ y'
    obtain ⟨m, hm, hm'⟩ := directed_of (· ≤ ·) k.unop k'.unop
    let b : Opposite.op m ⟶ k := (homOfLE hm).op
    let b' : Opposite.op m ⟶ k' := (homOfLE hm').op
    have hbb : b' ≫ a' = b ≫ a := Subsingleton.elim _ _
    refine ⟨Opposite.op m, b ≫ a, (pushforwardTransition F b a).hom.app (op V₀) x₀,
      (pushforwardTransition F b' a').hom.app (op V₀) x₀', ?_, ?_⟩
    · rw [← hx₀, ← pushforwardTransition_comp_pushforwardLeg c F ιC hιC b a]
      rfl
    · rw [← hx₀', ← pushforwardTransition_comp_pushforwardLeg c F ιC hιC b' a', hbb]
      rfl
  -- bijectivity on the base changes of quasi-compact quasi-separated objects of the stages
  have hgood : ∀ (i₀ : Iᵒᵖ) (V₀ : (D.obj i₀).Etale) [CompactSpace V₀.left]
      [QuasiSeparatedSpace V₀.left],
      Function.Bijective (κ.hom.app (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀))) := by
    intro i₀ V₀ _ _
    refine ⟨fun y y' hy => ?_, fun s => ?_⟩
    · obtain ⟨m, a, x, x', rfl, rfl⟩ := hcommon i₀ V₀ y y'
      have hx : (pushforwardLeg c F ψ a).hom.app (op V₀) x =
          (pushforwardLeg c F ψ a).hom.app (op V₀) x' :=
        ((happ a V₀ x).symm.trans hy).trans (happ a V₀ x')
      obtain ⟨l, b, hb⟩ := hinj i₀ V₀ a x x' hx
      rw [← pushforwardTransition_comp_pushforwardLeg c F ιC hιC b a]
      change (pushforwardLeg c F ιC (b ≫ a)).hom.app (op V₀)
          ((pushforwardTransition F b a).hom.app (op V₀) x) =
        (pushforwardLeg c F ιC (b ≫ a)).hom.app (op V₀)
          ((pushforwardTransition F b a).hom.app (op V₀) x')
      rw [hb]
    · obtain ⟨k, a, x, rfl⟩ := hsurj i₀ V₀ s
      exact ⟨(pushforwardLeg c F ιC a).hom.app (op V₀) x, happ a V₀ x⟩
  -- the comparison is locally bijective, hence an isomorphism
  have hiso : IsIso κ := by
    refine (Sheaf.isLocallyBijective_iff_isIso κ).mp ⟨⟨fun {X} x y hxy => ?_⟩, ⟨fun {U} s => ?_⟩⟩
    · choose i₀ V₀ hc₁ hc₂ f hf using exists_smallEtaleBaseChange_hom_mem_range hc X.unop
      refine (smallEtaleTopology c.pt).superset_covering ?_
        ((Scheme.ofArrows_mem_smallEtaleTopology_iff f).2
          (Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 ⟨z, hf z⟩))
      refine (Sieve.generate_le_iff _ _).2 ?_
      rintro V g ⟨z⟩
      have := hc₁ z
      have := hc₂ z
      apply (hgood (i₀ z) (V₀ z)).1
      change (κ.hom.app _) (C.obj.map (f z).op x) = (κ.hom.app _) (C.obj.map (f z).op y)
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        κ.hom.naturality, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      exact congrArg _ hxy
    · choose i₀ V₀ hc₁ hc₂ f hf using exists_smallEtaleBaseChange_hom_mem_range hc U
      refine (smallEtaleTopology c.pt).superset_covering ?_
        ((Scheme.ofArrows_mem_smallEtaleTopology_iff f).2
          (Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 ⟨z, hf z⟩))
      refine (Sieve.generate_le_iff _ _).2 ?_
      rintro V g ⟨z⟩
      have := hc₁ z
      have := hc₂ z
      exact (hgood (i₀ z) (V₀ z)).2 _
  exact (hC.of_iso (asIso κ)).congr_legs hκ

end Criterion

/-! ### The colimit formula -/

section DirectImage

open LimitHigherDirectImage LimitDirectImage

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}}
  (γ : DX ⟶ DS) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] {cX : Cone DX} {cS : Cone DS} (hcX : IsLimit cX)
  (hcS : IsLimit cS)

include hcX in
/-- **The degree zero case of [Stacks, Tag 0EYM] for sheaves of sets.** Let `g_i : X_i ⟶ S_i` be
quasi-compact and quasi-separated with affine transition morphisms, `g` the limit morphism, and
`ι_i : f_i⁻¹F_i ⟶ 𝓕` present `𝓕 = colim f_i⁻¹F_i` for a system of sheaves of sets. Then the
maps `h_i⁻¹g_{i, *}F_i ⟶ g_*𝓕` of `Stacks.EtaleCohomology.LimitDirectImage.baseChangeProjectionMap`
present `g_*𝓕 = colim h_i⁻¹g_{i, *}F_i`. -/
theorem isSheafPullbackColimitPresentation_projectionMap (F : EtaleSheafSystem DX (Type (u + 1)))
    {𝓕 : Sheaf (smallEtaleTopology cX.pt) (Type (u + 1))}
    (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback (Type (u + 1)) (X := cX.pt) (cX.π.app i)).obj
      (F.obj i) ⟶ 𝓕)
    (hι : F.IsSheafPullbackCocone cX ι) (hpres : F.IsSheafPullbackColimitPresentation cX 𝓕 ι) :
    (pushforwardSystem (Type (u + 1)) γ F).IsSheafPullbackColimitPresentation cS
      ((smallEtalePushforward (limitMorphism γ cX cS hcS) (Type (u + 1))).obj 𝓕)
      (baseChangeProjectionMap (Type (u + 1)) γ cX hcS F ι) := by
  let g := limitMorphism γ cX cS hcS
  let F' := pushforwardSystem (Type (u + 1)) γ F
  let ψ := baseChangeProjectionMap (Type (u + 1)) γ cX hcS F ι
  have hψ : F'.IsSheafPullbackCocone cS ψ :=
    isSheafPullbackCocone_baseChangeProjectionMap (Type (u + 1)) γ cX hcS F ι hι
  let Φ : ∀ i₀ : Iᵒᵖ, (smallEtalePushforward (γ.app i₀) (Type (u + 1))).obj
      ((smallEtalePushforward (X := cX.pt) (cX.π.app i₀) (Type (u + 1))).obj 𝓕) ≅
        (smallEtalePushforward (X := cS.pt) (cS.π.app i₀) (Type (u + 1))).obj
          ((smallEtalePushforward g (Type (u + 1))).obj 𝓕) := fun i₀ =>
    (smallEtaleSheafSquarePushforwardComp (Type (u + 1)) (X' := cS.pt) (Y := cX.pt)
      (cS.π.app i₀) (γ.app i₀) g (cX.π.app i₀) (limitMorphism_comp_π γ cX cS hcS i₀)).app 𝓕
  let Ψ : ∀ {k i₀ : Iᵒᵖ} (a : k ⟶ i₀), (smallEtalePushforward (γ.app i₀) (Type (u + 1))).obj
      ((smallEtalePushforward (DX.map a) (Type (u + 1))).obj (F.obj k)) ≅
        (smallEtalePushforward (DS.map a) (Type (u + 1))).obj (F'.obj k) := fun {k i₀} a =>
    (smallEtaleSheafSquarePushforwardComp (Type (u + 1)) (DS.map a) (γ.app i₀) (γ.app k)
      (DX.map a) (transition_comm γ a)).app (F.obj k)
  have hleg : ∀ {k i₀ : Iᵒᵖ} (a : k ⟶ i₀),
      (smallEtalePushforward (γ.app i₀) (Type (u + 1))).map (pushforwardLeg cX F ι a) ≫
        (Φ i₀).hom = (Ψ a).hom ≫ pushforwardLeg cS F' ψ a := fun {k i₀} a =>
    smallEtalePushforward_map_comp_smallEtaleSheafSquarePushforwardComp (Type (u + 1))
      (X₂ := cX.pt) (S₂ := cS.pt) (γ.app i₀) (γ.app k) g (DX.map a) (DS.map a) (cX.π.app k)
      (cS.π.app k) (cX.π.app i₀) (cS.π.app i₀) (cX.w a).symm (cS.w a).symm (transition_comm γ a)
      (limitMorphism_comp_π γ cX cS hcS k) (limitMorphism_comp_π γ cX cS hcS i₀) (ι k)
  have htr : ∀ {l k i₀ : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ i₀),
      (smallEtalePushforward (γ.app i₀) (Type (u + 1))).map (pushforwardTransition F b a) ≫
        (Ψ (b ≫ a)).hom = (Ψ a).hom ≫ pushforwardTransition F' b a := fun {l k i₀} b a =>
    smallEtalePushforward_map_comp_smallEtaleSheafSquarePushforwardComp (Type (u + 1))
      (γ.app i₀) (γ.app k) (γ.app l) (DX.map a) (DS.map a) (DX.map b) (DS.map b)
      (DX.map (b ≫ a)) (DS.map (b ≫ a)) (DX.map_comp b a) (DS.map_comp b a)
      (transition_comm γ a) (transition_comm γ b) (transition_comm γ (b ≫ a)) (F.map b)
  have hleg' : ∀ {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) (V₀ : (DS.obj i₀).Etale)
      (y : (F.obj k).obj.obj (op ((smallEtaleBaseChange (DX.map a)).obj
        ((smallEtaleBaseChange (γ.app i₀)).obj V₀)))),
      (pushforwardLeg cS F' ψ a).hom.app (op V₀) ((Ψ a).hom.hom.app (op V₀) y) =
        (Φ i₀).hom.hom.app (op V₀)
          ((pushforwardLeg cX F ι a).hom.app (op ((smallEtaleBaseChange (γ.app i₀)).obj V₀)) y) :=
    fun a V₀ y => (congrArg (fun φ => φ.hom.app (op V₀) y) (hleg a)).symm
  have htr' : ∀ {l k i₀ : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ i₀) (V₀ : (DS.obj i₀).Etale)
      (y : (F.obj k).obj.obj (op ((smallEtaleBaseChange (DX.map a)).obj
        ((smallEtaleBaseChange (γ.app i₀)).obj V₀)))),
      (pushforwardTransition F' b a).hom.app (op V₀) ((Ψ a).hom.hom.app (op V₀) y) =
        (Ψ (b ≫ a)).hom.hom.app (op V₀)
          ((pushforwardTransition F b a).hom.app
            (op ((smallEtaleBaseChange (γ.app i₀)).obj V₀)) y) :=
    fun b a V₀ y => (congrArg (fun φ => φ.hom.app (op V₀) y) (htr b a)).symm
  have hinv : ∀ {Z : Scheme.{u}} {P Q : Sheaf (smallEtaleTopology Z) (Type (u + 1))} (e : P ≅ Q)
      (V : Z.Etaleᵒᵖ) (z : Q.obj.obj V), e.hom.hom.app V (e.inv.hom.app V z) = z :=
    fun e V z => congrArg (fun φ => φ.hom.app V z) e.inv_hom_id
  have hinj' : ∀ {Z : Scheme.{u}} {P Q : Sheaf (smallEtaleTopology Z) (Type (u + 1))} (e : P ≅ Q)
      (V : Z.Etaleᵒᵖ) {z z' : P.obj.obj V}, e.hom.hom.app V z = e.hom.hom.app V z' → z = z' :=
    fun e V z z' h => (congrArg (fun φ => φ.hom.app V z) e.hom_inv_id).symm.trans
      ((congrArg (e.inv.hom.app V) h).trans (congrArg (fun φ => φ.hom.app V z') e.hom_inv_id))
  refine isSheafPullbackColimitPresentation_of_forall_exists hcS F' ψ hψ ?_ ?_
  · intro i₀ V₀ _ _ s
    let W₀ := (smallEtaleBaseChange (γ.app i₀)).obj V₀
    have : CompactSpace W₀.left :=
      compactSpace_smallEtaleBaseChange_obj (γ.app i₀) V₀ inferInstance
    have : QuasiSeparatedSpace W₀.left :=
      quasiSeparatedSpace_smallEtaleBaseChange_obj (γ.app i₀) V₀ inferInstance
    obtain ⟨k, a, y, hy⟩ := exists_pushforwardLeg_apply_eq cX hcX F ι hι hpres W₀
      ((Φ i₀).inv.hom.app (op V₀) s)
    refine ⟨k, a, (Ψ a).hom.hom.app (op V₀) y, ?_⟩
    refine (hleg' a V₀ y).trans ?_
    change (Φ i₀).hom.hom.app (op V₀) ((pushforwardLeg cX F ι a).hom.app (op W₀) y) = s
    rw [hy]
    exact hinv (Φ i₀) (op V₀) s
  · intro i₀ V₀ _ _ k a x x' hx
    let W₀ := (smallEtaleBaseChange (γ.app i₀)).obj V₀
    have : CompactSpace W₀.left :=
      compactSpace_smallEtaleBaseChange_obj (γ.app i₀) V₀ inferInstance
    have : QuasiSeparatedSpace W₀.left :=
      quasiSeparatedSpace_smallEtaleBaseChange_obj (γ.app i₀) V₀ inferInstance
    let y := (Ψ a).inv.hom.app (op V₀) x
    let y' := (Ψ a).inv.hom.app (op V₀) x'
    have hxy : (Ψ a).hom.hom.app (op V₀) y = x := hinv (Ψ a) (op V₀) x
    have hxy' : (Ψ a).hom.hom.app (op V₀) y' = x' := hinv (Ψ a) (op V₀) x'
    have h := hleg' a V₀ y
    have h' := hleg' a V₀ y'
    rw [hxy] at h
    rw [hxy'] at h'
    have hy : (pushforwardLeg cX F ι a).hom.app (op W₀) y =
        (pushforwardLeg cX F ι a).hom.app (op W₀) y' :=
      hinj' (Φ i₀) (op V₀) (h.symm.trans (hx.trans h'))
    obtain ⟨l, b, hb⟩ := exists_pushforwardTransition_apply_eq cX hcX F ι hι hpres W₀ a y y' hy
    refine ⟨l, b, ?_⟩
    have h2 := htr' b a V₀ y
    have h2' := htr' b a V₀ y'
    rw [hxy] at h2
    rw [hxy'] at h2'
    refine h2.trans (Eq.trans ?_ h2'.symm)
    change (Ψ (b ≫ a)).hom.hom.app (op V₀) ((pushforwardTransition F b a).hom.app (op W₀) y) =
      (Ψ (b ≫ a)).hom.hom.app (op V₀) ((pushforwardTransition F b a).hom.app (op W₀) y')
    rw [hb]

end DirectImage

end Stacks.EtaleCohomology.Sets

end
