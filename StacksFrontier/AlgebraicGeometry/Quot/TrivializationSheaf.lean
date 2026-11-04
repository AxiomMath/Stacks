module

public import StacksFrontier.AlgebraicGeometry.Quot.TrivializationTorsor
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackModuleHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent

/-!
# The trivialisations of a quasi-coherent module form an fppf sheaf

Let `U` be a scheme of the big fppf site of `S` and `N` a module on the small étale site of the
algebraic space `U`.  The trivialisations `𝒪_V ≅ (V ⟶ U)^*N` over the schemes `V` of the site of
`U` form a presheaf `Isom(𝒪, N)` (`AlgebraicGeometry.Space.trivializationsSitePresheaf`).  This
file proves that it is a sheaf for the fppf topology when `N` is quasi-coherent, in particular
when `N` is invertible.

## Main definitions

* `AlgebraicGeometry.Space.trivializationModuleHom`: a trivialisation `𝒪_W ≅ b^*N`, read along
  `r : W ⟶ V` with `r ≫ a = b` as an isomorphism `r^*𝒪_V ⟶ r^*a^*N` of inverse images.

## Main results

* `AlgebraicGeometry.Space.moduleHomRefine_trivializationModuleHom`: the restriction of that
  homomorphism to a refinement is the homomorphism of the inverse image of the trivialisation.
* `AlgebraicGeometry.Space.trivializationPullback_eq_of_compatible`: a compatible family of
  trivialisations agrees over any scheme mapping compatibly to two members.
* `AlgebraicGeometry.Space.isSheaf_trivializationsSliceFunctor`: the trivialisations of a
  quasi-coherent module form a sheaf of large types for the fppf topology.
* `AlgebraicGeometry.Space.isSheaf_trivializationsSitePresheaf_of_isQuasicoherentOnSite` and
  `AlgebraicGeometry.Space.isSheaf_trivializationsSitePresheaf`: the same for the presheaf in the
  universe of the site, for a quasi-coherent and for an invertible module.
* `AlgebraicGeometry.Space.exists_iso_yoneda_trivializationsSitePresheaf`: for an invertible
  module, `Isom(𝒪, N)` is represented by a scheme smooth, surjective and affine over `U`.
* `AlgebraicGeometry.Space.exists_universal_trivializationsPresheaf`: for an invertible module,
  there is a universal trivialisation over a scheme smooth and surjective over `U`.

## Implementation notes

A compatible family of trivialisations `α_f` over the members `f : W ⟶ V` of a covering sieve is
read, through `AlgebraicGeometry.Space.trivializationModuleHom`, as a family of isomorphisms
`f^*𝒪_V ⟶ f^*(V ⟶ U)^*N`; by Descent, Proposition 023T for quasi-coherent modules
(`AlgebraicGeometry.Space.existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible`) it
descends to a homomorphism `𝒪_V ⟶ (V ⟶ U)^*N`, and the inverses descend to its inverse.  The
compatibility asked for by the descent statement is over an arbitrary algebraic space mapping to
two members; such a space factors through the space represented by the fibre product of the two
schemes, where the compatibility of the family applies.

## References

* [Stacks Project, Tag 0D2A](https://stacks.math.columbia.edu/tag/0D2A)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Functor

/-- **Conjugating a transported morphism along a composite**: for identifications
`Uᵢⱼ : Oᵢ ≅ Eᵢⱼ Oⱼ` and transport isomorphisms `Θᵢⱼ : Eᵢⱼ Mⱼ ≅ Mᵢ` compatible with
`Th : E₁₃ ≅ E₂₃ ⋙ E₁₂`, conjugating by `Th` the morphism `E₂₃ O₃ ⟶ E₂₃ M₃` read off
`α : O₂ ⟶ M₂` is the morphism `E₁₃ O₃ ⟶ E₁₃ M₃` read off the transport of `α` along `E₁₂`. -/
theorem conjHom_transport_comp {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] {E₁₂ : C₂ ⥤ C₁} {E₂₃ : C₃ ⥤ C₂} {E₁₃ : C₃ ⥤ C₁} (Th : E₁₃ ≅ E₂₃ ⋙ E₁₂)
    {O₁ : C₁} {O₂ : C₂} {O₃ : C₃} (U₁₂ : O₁ ≅ E₁₂.obj O₂) (U₂₃ : O₂ ≅ E₂₃.obj O₃)
    (U₁₃ : O₁ ≅ E₁₃.obj O₃) (hU : U₁₃.symm = Th.app O₃ ≪≫ E₁₂.mapIso U₂₃.symm ≪≫ U₁₂.symm)
    {M₁ : C₁} {M₂ : C₂} {M₃ : C₃} (Θ₁₂ : E₁₂.obj M₂ ≅ M₁) (Θ₂₃ : E₂₃.obj M₃ ≅ M₂)
    (Θ₁₃ : E₁₃.obj M₃ ≅ M₁) (hΘ : Θ₁₃ = Th.app M₃ ≪≫ E₁₂.mapIso Θ₂₃ ≪≫ Θ₁₂)
    (α : O₂ ⟶ M₂) :
    conjHom Th (U₂₃.inv ≫ α ≫ Θ₂₃.inv) =
      U₁₃.inv ≫ (U₁₂.hom ≫ E₁₂.map α ≫ Θ₁₂.hom) ≫ Θ₁₃.inv := by
  subst hΘ
  have hU' : U₁₃.inv = Th.hom.app O₃ ≫ E₁₂.map U₂₃.inv ≫ U₁₂.inv := by
    simpa using congrArg Iso.hom hU
  rw [hU']
  simp [conjHom]

end CategoryTheory.Functor

namespace CategoryTheory.Functor

universe w v₁ v₂ u₁ u₂

/-- **A presheaf whose restriction along a fully faithful, essentially surjective functor is
represented has a universal element.**  If `L.op ⋙ F ≅ h_{W₀}`, then every `T` receives a bijection
`(T ⟶ L W₀) ≃ F(T)`, `k ↦ k^*τ`, for the element `τ` named by `𝟙 W₀`. -/
theorem bijective_map_of_iso_yoneda {A : Type u₁} [Category.{v₁} A] {B : Type u₂}
    [Category.{v₁} B] (L : A ⥤ B) (hL : L.FullyFaithful) (Lpre : B → A)
    (e : ∀ T : B, L.obj (Lpre T) ≅ T) (F : Bᵒᵖ ⥤ Type (v₁ + 1)) {W₀ : A}
    (j : L.op ⋙ F ≅ yoneda.obj W₀ ⋙ uliftFunctor.{v₁ + 1}) (T : B) :
    Function.Bijective
      (fun k : T ⟶ L.obj W₀ ↦ F.map k.op (j.inv.app (op W₀) (ULift.up (𝟙 W₀)))) := by
  set τ := j.inv.app (op W₀) (ULift.up (𝟙 W₀))
  have key : ∀ {V : A} (k₀ : V ⟶ W₀), F.map (L.map k₀).op τ = j.inv.app (op V) (ULift.up k₀) := by
    intro V k₀
    let x₀ : (yoneda.obj W₀ ⋙ uliftFunctor.{v₁ + 1}).obj (op W₀) := ULift.up (𝟙 W₀)
    have hn := ConcreteCategory.congr_hom (j.inv.naturality k₀.op) x₀
    rw [types_comp_apply, types_comp_apply] at hn
    refine hn.symm.trans ?_
    exact congrArg (fun m ↦ j.inv.app (op V) (ULift.up m)) (Category.comp_id k₀)
  have hsite : ∀ V : A, Function.Bijective (fun k : L.obj V ⟶ L.obj W₀ ↦ F.map k.op τ) := by
    intro V
    have hcomp : (fun k : L.obj V ⟶ L.obj W₀ ↦ F.map k.op τ) =
        (fun k₀ ↦ j.inv.app (op V) (ULift.up k₀)) ∘ hL.homEquiv.symm := by
      funext k
      rw [Function.comp_apply, ← key]
      exact congrArg (fun m ↦ F.map m.op τ) (hL.homEquiv.apply_symm_apply k).symm
    rw [hcomp]
    exact (((j.app (op V)).toEquiv.symm.bijective).comp Equiv.ulift.symm.bijective).comp
      hL.homEquiv.symm.bijective
  have hfun : (fun k : T ⟶ L.obj W₀ ↦ F.map k.op τ) =
      (F.map (e T).inv.op) ∘ (fun k ↦ F.map k.op τ) ∘ (fun k ↦ (e T).hom ≫ k) := by
    funext k
    simp only [Function.comp_apply]
    rw [← types_comp_apply (F.map _) (F.map _), ← F.map_comp, ← op_comp, Iso.inv_hom_id_assoc]
  rw [hfun]
  refine ((F.mapIso (e T).symm.op).toEquiv.bijective.comp (hsite _)).comp ?_
  refine ⟨fun a b h ↦ (cancel_epi (e T).hom).1 h, fun k ↦ ⟨(e T).inv ≫ k, ?_⟩⟩
  exact Iso.hom_inv_id_assoc _ _

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section ModuleHom

variable {V W Y Z : AlgebraicSpaces B S hS} (N : Modules.{u, u} B S hS Z.1 Z.2)

/-- **A trivialisation read as a homomorphism of inverse images.**  For `r : W ⟶ V` with
`r ≫ a = b`, a trivialisation `𝒪_W ≅ b^*N` gives `r^*𝒪_V ≅ 𝒪_W ≅ b^*N ≅ r^*a^*N`. -/
def trivializationModuleHom {a : V ⟶ Z} {b : W ⟶ Z} (r : W ⟶ V) (h : r ≫ a = b)
    (α : structureModule W ≅ (modulePullback B S hS b).obj N) :
    (modulePullback B S hS r).obj (structureModule V) ⟶
      (modulePullback B S hS r).obj ((modulePullback B S hS a).obj N) :=
  (structureModulePullbackIso r).inv ≫ α.hom ≫ (modulePullbackTriangle B S hS h).hom.app N

/-- The homomorphism attached to a trivialisation is an isomorphism. -/
instance isIso_trivializationModuleHom {a : V ⟶ Z} {b : W ⟶ Z} (r : W ⟶ V) (h : r ≫ a = b)
    (α : structureModule W ≅ (modulePullback B S hS b).obj N) :
    IsIso (trivializationModuleHom N r h α) := by
  rw [trivializationModuleHom]
  infer_instance

/-- The homomorphism attached to the inverse image of a trivialisation `β` is the inverse image
of `β`. -/
theorem trivializationModuleHom_trivializationPullback {a : V ⟶ Z} {b : W ⟶ Z} (r : W ⟶ V)
    (h : r ≫ a = b) (β : structureModule V ≅ (modulePullback B S hS a).obj N) :
    trivializationModuleHom N r h (trivializationPullback N r h β) =
      (modulePullback B S hS r).map β.hom := by
  rw [trivializationModuleHom, trivializationPullback_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id,
    Iso.inv_hom_id_assoc]

/-- A trivialisation is determined by its attached homomorphism. -/
theorem trivializationModuleHom_injective {a : V ⟶ Z} {b : W ⟶ Z} (r : W ⟶ V) (h : r ≫ a = b)
    {α α' : structureModule W ≅ (modulePullback B S hS b).obj N}
    (he : trivializationModuleHom N r h α = trivializationModuleHom N r h α') : α = α' := by
  ext1
  have h' := congrArg (fun m ↦ (structureModulePullbackIso r).hom ≫ m ≫
    (modulePullbackTriangle B S hS h).inv.app N) he
  simpa only [trivializationModuleHom, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    Iso.hom_inv_id_assoc] using h'

/-- **The restriction of the homomorphism attached to a trivialisation to a refinement** is the
homomorphism attached to the inverse image of the trivialisation. -/
theorem moduleHomRefine_trivializationModuleHom {a : V ⟶ Z} {b : W ⟶ Z} {c : Y ⟶ Z}
    (r : W ⟶ V) (s : Y ⟶ W) {k : Y ⟶ V} (h : r ≫ a = b) (hk : s ≫ r = k) (hs : s ≫ b = c)
    (hc : k ≫ a = c) (α : structureModule W ≅ (modulePullback B S hS b).obj N) :
    moduleHomRefine hk (structureModule V) ((modulePullback B S hS a).obj N)
        (trivializationModuleHom N r h α) =
      trivializationModuleHom N k hc (trivializationPullback N s hs α) := by
  subst hk hc
  exact Functor.conjHom_transport_comp _ _ _ _
    (ModulePushforwardCoherence.structureModulePullbackIso_symm_of_comp s r rfl) _ _ _
    (modulePullbackTriangle_app_symm_comp N r s h hs rfl) α.hom

end ModuleHom

section Sheaf

variable (U : BigFppfOver B S hS)
  (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
    ((schemeSpaceFunctor B S hS).obj U).2)

/-- The structure map of the iterated slice of `f : W ⟶ V` is compatible with `f`. -/
private theorem map_iteratedSliceBackward_left_comp_hom {V W : BigFppfOver B U.left.1 U.left.2}
    (f : W ⟶ V) :
    (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.map f).left ≫
      (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.obj V).hom =
    (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.obj W).hom := by
  rw [← Functor.map_comp, Over.w (U.iteratedSliceBackward.map f)]

/-- **A compatible family of trivialisations agrees over a scheme mapping to two members.**  If
`Q` maps to the members `f₁` and `f₂` of a presieve on `V` compatibly over `V`, the inverse
images to `Q` of the trivialisations over `f₁` and over `f₂` agree. -/
theorem trivializationPullback_eq_of_compatible {V : BigFppfOver B U.left.1 U.left.2}
    {R : Presieve V} {x : Presieve.FamilyOfElements (trivializationsSliceFunctor U N) R}
    (hx : x.Compatible) {W₁ W₂ : BigFppfOver B U.left.1 U.left.2} {f₁ : W₁ ⟶ V} {f₂ : W₂ ⟶ V}
    (h₁ : R f₁) (h₂ : R f₂) {Q : BigFppfOver B S hS}
    (u₁ : Q ⟶ (U.iteratedSliceBackward.obj W₁).left)
    (u₂ : Q ⟶ (U.iteratedSliceBackward.obj W₂).left)
    (hu : u₁ ≫ (U.iteratedSliceBackward.map f₁).left =
      u₂ ≫ (U.iteratedSliceBackward.map f₂).left)
    {c : (schemeSpaceFunctor B S hS).obj Q ⟶ (schemeSpaceFunctor B S hS).obj U}
    (hc₁ : (schemeSpaceFunctor B S hS).map u₁ ≫
      (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.obj W₁).hom = c)
    (hc₂ : (schemeSpaceFunctor B S hS).map u₂ ≫
      (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.obj W₂).hom = c) :
    trivializationPullback N ((schemeSpaceFunctor B S hS).map u₁) hc₁ (x f₁ h₁) =
      trivializationPullback N ((schemeSpaceFunctor B S hS).map u₂) hc₂ (x f₂ h₂) := by
  have hl : u₁.left ≫ f₁.left = u₂.left ≫ f₂.left := congrArg CommaMorphism.left hu
  let Q' : BigFppfOver B U.left.1 U.left.2 := Over.mk (u₁.left ≫ W₁.hom)
  let g₁ : Q' ⟶ W₁ := Over.homMk u₁.left rfl
  let g₂ : Q' ⟶ W₂ := Over.homMk u₂.left
    ((congrArg (u₂.left ≫ ·) (Over.w f₂)).symm.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ V.hom) hl).symm.trans ((Category.assoc _ _ _).trans
        (congrArg (u₁.left ≫ ·) (Over.w f₁))))))
  have hg : g₁ ≫ f₁ = g₂ ≫ f₂ := Over.OverMorphism.ext hl
  have hx' := hx g₁ g₂ h₁ h₂ hg
  let e : Q ⟶ (U.iteratedSliceBackward.obj Q').left := Over.homMk (𝟙 Q.left)
    ((Category.id_comp _).trans ((Category.assoc _ _ _).trans (Over.w u₁)))
  have he₁ : e ≫ (U.iteratedSliceBackward.map g₁).left = u₁ :=
    Over.OverMorphism.ext (Category.id_comp _)
  have he₂ : e ≫ (U.iteratedSliceBackward.map g₂).left = u₂ :=
    Over.OverMorphism.ext (Category.id_comp _)
  have hec : (schemeSpaceFunctor B S hS).map e ≫
      (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.obj Q').hom = c := by
    rw [← hc₁, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Over.OverMorphism.ext (Category.id_comp _))
  have step : ∀ {W : BigFppfOver B U.left.1 U.left.2} {f : W ⟶ V} (hf : R f) (g : Q' ⟶ W)
      (u : Q ⟶ (U.iteratedSliceBackward.obj W).left)
      (hu : e ≫ (U.iteratedSliceBackward.map g).left = u)
      (hc : (schemeSpaceFunctor B S hS).map u ≫
        (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.obj W).hom = c),
      trivializationPullback N ((schemeSpaceFunctor B S hS).map u) hc (x f hf) =
        trivializationPullback N ((schemeSpaceFunctor B S hS).map e) hec
          ((trivializationsSliceFunctor U N).map g.op (x f hf)) := by
    intro W f hf g u hu hc
    subst hu
    rw [trivializationsSliceFunctor_map_apply U N g.op]
    exact (trivializationPullback_congr N (Functor.map_comp _ _ _) _
      (by rw [Category.assoc, map_iteratedSliceBackward_left_comp_hom, hec]) _).trans
      (trivializationPullback_comp N _ _ (map_iteratedSliceBackward_left_comp_hom U g) hec _ _)
  exact (step h₁ g₁ u₁ he₁ hc₁).trans
    ((congrArg _ hx').trans (step h₂ g₂ u₂ he₂ hc₂).symm)

/-- **The trivialisations of a quasi-coherent module form an fppf sheaf**, as a presheaf of
large types on the site of `U`.  A compatible family over a covering sieve descends, together
with the family of inverses, by Descent, Proposition 023T for quasi-coherent modules. -/
theorem isSheaf_trivializationsSliceFunctor (hN : N.IsQuasicoherentOnSite) :
    Presieve.IsSheaf (BigFppfOver.topology B U.left.1 U.left.2)
      (trivializationsSliceFunctor U N) := by
  intro V R hR x hx
  have hri : ∀ i : Σ W : BigFppfOver B U.left.1 U.left.2, {f : W ⟶ V // R f},
      (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.map i.2.1).left ≫
        (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.obj V).hom =
      (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.obj i.1).hom := fun i ↦
    map_iteratedSliceBackward_left_comp_hom U i.2.1
  have hM : (structureModule ((schemeSpaceFunctor B S hS).obj
      (U.iteratedSliceBackward.obj V).left)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertibleModule _ _ (isInvertibleModule_structureModule _)
  have hP : ((modulePullback B S hS ((schemeSpaceFunctor B S hS).map
      (U.iteratedSliceBackward.obj V).hom)).obj N).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ N hN
  have hr : Sieve.generate (Presieve.ofArrows
      (fun i : Σ W : BigFppfOver B U.left.1 U.left.2, {f : W ⟶ V // R f} ↦
        (U.iteratedSliceBackward.obj i.1).left)
      (fun i ↦ (U.iteratedSliceBackward.map i.2.1).left)) ∈
      BigFppfOver.topology B S hS (U.iteratedSliceBackward.obj V).left := by
    refine (GrothendieckTopology.mem_over_iff _ _).2
      (B.topology.superset_covering ?_ ((B.topology.mem_over_iff R).1 hR))
    intro Z g hg
    refine (Sieve.overEquiv_iff _ g).2 ?_
    have hg' := (Sieve.overEquiv_iff R g).1 hg
    let i : Σ W : BigFppfOver B U.left.1 U.left.2, {f : W ⟶ V // R f} := ⟨_, _, hg'⟩
    let k : (Over.mk (g ≫ (U.iteratedSliceBackward.obj V).left.hom) : BigFppfOver B S hS) ⟶
        (U.iteratedSliceBackward.obj i.1).left :=
      Over.homMk (𝟙 Z) ((Category.id_comp _).trans (Category.assoc _ _ _))
    have hk : k ≫ (U.iteratedSliceBackward.map i.2.1).left = Over.homMk g :=
      Over.OverMorphism.ext (Category.id_comp _)
    have hmem := (Sieve.generate _).downward_closed
      (Sieve.le_generate (Presieve.ofArrows
        (fun i : Σ W : BigFppfOver B U.left.1 U.left.2, {f : W ⟶ V // R f} ↦
          (U.iteratedSliceBackward.obj i.1).left)
        (fun i ↦ (U.iteratedSliceBackward.map i.2.1).left)) _ _ (Presieve.ofArrows.mk i)) k
    rwa [hk] at hmem
  have hα : ModuleHomFamilyCompatible _ _
      (fun i : Σ W : BigFppfOver B U.left.1 U.left.2, {f : W ⟶ V // R f} ↦
        (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.map i.2.1).left)
      (fun i ↦ trivializationModuleHom N _ (hri i) (x i.2.1 i.2.2)) := by
    intro Y i j a b h
    have hpb : IsPullback
        ((schemeSpaceFunctor B S hS).map (pullback.fst (U.iteratedSliceBackward.map i.2.1).left
          (U.iteratedSliceBackward.map j.2.1).left))
        ((schemeSpaceFunctor B S hS).map (pullback.snd (U.iteratedSliceBackward.map i.2.1).left
          (U.iteratedSliceBackward.map j.2.1).left))
        ((schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.map i.2.1).left)
        ((schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.map j.2.1).left) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _)
        ((IsPullback.of_hasPullback _ _).map yoneda)
    obtain ⟨l, rfl, rfl⟩ := hpb.exists_lift a b h
    have hjc := hpb.w =≫ (schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.obj V).hom
    simp only [Category.assoc, hri] at hjc
    refine (moduleHomRefine_trivializationModuleHom N _ _ (hri i) rfl
      (by simp only [Category.assoc, hri]) rfl _).trans ?_
    refine Eq.trans ?_ (moduleHomRefine_trivializationModuleHom N _ _ (hri j) h.symm
      (by simp only [Category.assoc, hri, hjc]) rfl _).symm
    refine congrArg (trivializationModuleHom N _ _) ?_
    refine (trivializationPullback_comp N _ _ rfl (by simp only [Category.assoc, hri])
      _ _).trans ?_
    refine Eq.trans ?_ (trivializationPullback_comp N _ _ hjc.symm
      (by simp only [Category.assoc, hri]) _ _).symm
    exact congrArg _ (trivializationPullback_eq_of_compatible U N hx i.2.2 j.2.2 _ _
      pullback.condition rfl hjc.symm)
  have hiso := fun i : Σ W : BigFppfOver B U.left.1 U.left.2, {f : W ⟶ V // R f} ↦
    isIso_trivializationModuleHom N _ (hri i) (x i.2.1 i.2.2)
  obtain ⟨b, hb, hbu⟩ := existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible _ _ _
    hM hP _ _ hr _ hα
  obtain ⟨c, hc, -⟩ := existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible _ _ _
    hP hM _ _ hr _ (hα.inv hiso)
  obtain ⟨e₁, -, hbc⟩ := existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible _ _ _
    hM hM _ _ hr _ (moduleHomFamilyCompatible_id _ _)
  obtain ⟨e₂, -, hcb⟩ := existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible _ _ _
    hP hP _ _ hr _ (moduleHomFamilyCompatible_id _ _)
  refine ⟨⟨b, c, ?_, ?_⟩, fun W f hf ↦ ?_, fun β hβ ↦ ?_⟩
  · refine (hbc _ fun i ↦ ?_).trans (hbc _ fun i ↦ ?_).symm
    · exact ((CategoryTheory.Functor.map_comp _ b c).trans
        (congrArg₂ (· ≫ ·) (hb i) (hc i))).trans (IsIso.hom_inv_id _)
    · exact CategoryTheory.Functor.map_id _ _
  · refine (hcb _ fun i ↦ ?_).trans (hcb _ fun i ↦ ?_).symm
    · exact ((CategoryTheory.Functor.map_comp _ c b).trans
        (congrArg₂ (· ≫ ·) (hc i) (hb i))).trans (IsIso.inv_hom_id _)
    · exact CategoryTheory.Functor.map_id _ _
  · refine (trivializationsSliceFunctor_map_apply U N f.op _).trans ?_
    refine trivializationModuleHom_injective N _ (hri ⟨W, f, hf⟩) ?_
    exact (trivializationModuleHom_trivializationPullback N _ _ _).trans (hb ⟨W, f, hf⟩)
  · refine Iso.ext (hbu β.hom fun i ↦ ?_)
    refine (trivializationModuleHom_trivializationPullback N _ (hri i) β).symm.trans ?_
    exact congrArg _ ((trivializationsSliceFunctor_map_apply U N i.2.1.op β).symm.trans
      (hβ i.2.1 i.2.2))

/-- **The trivialisations of a quasi-coherent module form an fppf sheaf**, as a presheaf in the
universe of the site. -/
theorem isSheaf_trivializationsSitePresheaf_of_isQuasicoherentOnSite
    (hN : N.IsQuasicoherentOnSite) :
    Presheaf.IsSheaf (BigFppfOver.topology B U.left.1 U.left.2)
      (trivializationsSitePresheaf U N) := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 (Presieve.isSheaf_iso _
    (shrinkSitePresheafIso _).symm (isSheaf_trivializationsSliceFunctor U N hN))

/-- **The trivialisations of an invertible module form an fppf sheaf**: `Isom(𝒪, N)` of the
proof of Stacks 0D2A is a sheaf on the big fppf site of `U`. -/
theorem isSheaf_trivializationsSitePresheaf
    (hN : IsInvertibleModule ((schemeSpaceFunctor B S hS).obj U) N) :
    Presheaf.IsSheaf (BigFppfOver.topology B U.left.1 U.left.2)
      (trivializationsSitePresheaf U N) :=
  isSheaf_trivializationsSitePresheaf_of_isQuasicoherentOnSite U N
    (isQuasicoherentOnSite_of_isInvertibleModule _ N hN)

end Sheaf

/-- **`Isom(𝒪_T, N)` is represented by a scheme smooth, surjective and affine over `T`**, for an
invertible module `N` on a scheme `T` of the site. -/
theorem exists_iso_yoneda_trivializationsSitePresheaf (U : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
      ((schemeSpaceFunctor B S hS).obj U).2)
    (hN : IsInvertibleModule ((schemeSpaceFunctor B S hS).obj U) N) :
    ∃ (W : BigFppfOver B U.left.1 U.left.2) (_ : trivializationsSitePresheaf U N ≅ yoneda.obj W),
      Smooth ((BigFppfOver.toScheme B U.left.1 U.left.2).map (Over.mkIdTerminal.from W)) ∧
      Surjective ((BigFppfOver.toScheme B U.left.1 U.left.2).map (Over.mkIdTerminal.from W)) ∧
      _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B U.left.1 U.left.2).map (Over.mkIdTerminal.from W)) :=
  exists_iso_yoneda_trivializationsSitePresheaf_of_isSheaf U N hN
    (isSheaf_trivializationsSitePresheaf U N hN)

/-- The presheaf of trivialisations on the schemes over `U` agrees, along the iterated slice, with
the presheaf of trivialisations on the big fppf site of `U`. -/
theorem trivializationsPresheaf_map_iteratedSliceBackward (U : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
      ((schemeSpaceFunctor B S hS).obj U).2)
    {V V' : BigFppfOver B U.left.1 U.left.2} (k : V ⟶ V')
    (x : (trivializationsPresheaf U N).obj (op (U.iteratedSliceBackward.obj V'))) :
    (trivializationsPresheaf U N).map (U.iteratedSliceBackward.map k).op x =
      (trivializationsSliceFunctor U N).map k.op x :=
  (trivializationsPresheaf_map_apply U N _ x).trans
    (trivializationsSliceFunctor_map_apply U N k.op x).symm

/-- The presheaf of trivialisations on the big fppf site of `U` is the presheaf of
trivialisations on the schemes over `U`, read along the iterated slice. -/
theorem trivializationsSliceFunctor_eq (U : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
      ((schemeSpaceFunctor B S hS).obj U).2) :
    trivializationsSliceFunctor U N = U.iteratedSliceBackward.op ⋙ trivializationsPresheaf U N :=
  rfl

/-- **`Isom(𝒪_T, N)` on the schemes over `T` has a universal trivialisation over a scheme
`W ⟶ T` which is smooth and surjective**: every trivialisation over `V ⟶ T` is the restriction of
the universal one along a unique morphism `V ⟶ W` over `T`. -/
theorem exists_universal_trivializationsPresheaf (U : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
      ((schemeSpaceFunctor B S hS).obj U).2)
    (hN : IsInvertibleModule ((schemeSpaceFunctor B S hS).obj U) N) :
    ∃ (W : Over U) (τ : (trivializationsPresheaf U N).obj (op W)),
      (∀ T : Over U, Function.Bijective
        (fun k : T ⟶ W ↦ (trivializationsPresheaf U N).map k.op τ)) ∧
      Smooth ((BigFppfOver.toScheme B S hS).map W.hom) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map W.hom) := by
  obtain ⟨W₀, i, hsm, hsu, -⟩ := exists_iso_yoneda_trivializationsSitePresheaf U N hN
  have hterm : Over.mkIdTerminal.from W₀ = Over.homMk W₀.hom (by simp) :=
    Over.mkIdTerminal.hom_ext _ _
  rw [hterm] at hsm hsu
  let j : U.iteratedSliceBackward.op ⋙ trivializationsPresheaf U N ≅
      yoneda.obj W₀ ⋙ uliftFunctor.{u + 1} :=
    eqToIso (trivializationsSliceFunctor_eq U N).symm ≪≫
      (shrinkSitePresheafIso (trivializationsSliceFunctor U N)).symm ≪≫
      Functor.isoWhiskerRight i uliftFunctor
  exact ⟨U.iteratedSliceBackward.obj W₀, _, Functor.bijective_map_of_iso_yoneda
    U.iteratedSliceBackward (Over.iteratedSliceEquiv U).symm.fullyFaithfulFunctor
    (U.iteratedSliceForward.obj) (fun T ↦ ((Over.iteratedSliceEquiv U).unitIso.app T).symm)
    (trivializationsPresheaf U N) j, hsm, hsu⟩

end AlgebraicGeometry.Space
