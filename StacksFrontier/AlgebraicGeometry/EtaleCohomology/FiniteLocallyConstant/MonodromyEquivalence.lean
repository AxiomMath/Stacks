module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.PointedGaloisCovering
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.UnibranchContinuousModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.LocalizedGeneralCoefficients
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The monodromy functor on sheaves trivialized by pointed Galois covers

Let `X` be an irreducible, geometrically unibranch scheme with a geometric point `x`, and let
`Λ` be a ring. This file shows that the monodromy module functor `Φ`
(`AlgebraicGeometry.monodromyModule`) is fully faithful on the sheaves of `Λ`-modules which are
constant on some pointed Galois cover, and that every finite `Λ`-module with a continuous
`π₁(X, x)`-action is, up to isomorphism, the monodromy module of the descent sheaf `D(N)` along
a pointed Galois cover, which is a finite type locally constant sheaf.

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.restrictGraph_top_map_actHom` — on the covering, the
  automorphism `h` acts on `D(N)(A) ≅ N` through `ρ(h⁻¹)`.
* `AlgebraicGeometry.EtaleGaloisCovering.isFiniteTypeLocallyConstant_descentSheaf` — `D(N)` is
  finite type locally constant for `N` finitely generated.
* `AlgebraicGeometry.surjective_galoisAut` — every automorphism of a pointed Galois cover comes
  from the fundamental group.

## References

* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

universe u r w v

namespace AlgebraicGeometry

namespace EtaleGaloisCovering

variable {X : Scheme.{u}} {H : Type w} [Group H] (G : EtaleGaloisCovering X H)

/-- The covering, as the final object of the slice at itself. -/
abbrev topOver : Over G.cover := Over.mk (𝟙 G.cover)

section Action

variable {Λ : Type r} [Ring Λ] {N : Type v} [AddCommGroup N] [Module Λ N]
  {ρ : H →* Module.End Λ N}

/-- **On the covering, the automorphism `h` acts on equivariant maps restricted to the
diagonal through `ρ(h⁻¹)`, after translating by `h`.** -/
theorem restrictGraph_top_map_actHom (h : H) (f : (G.descentPresheaf Λ N ρ).obj (op G.cover))
    (y : G.cover.left) :
    G.restrictGraph Λ N ρ G.topOver (((G.descentPresheaf Λ N ρ).map (G.actHom h).op).hom f) y =
      ρ h⁻¹ (G.restrictGraph Λ N ρ G.topOver f ((G.act h).base y)) := by
  obtain ⟨g, hg⟩ : ∃ g : G.cover.left ⟶ G.fiberProd G.cover,
      g = G.graph G.topOver ≫ G.pullbackMap (G.actHom h) := ⟨_, rfl⟩
  have hg₁ : g ≫ pullback.fst _ _ = G.act h := by
    rw [hg, Category.assoc, pullbackMap_fst, ← Category.assoc, graph_fst]
    exact Category.id_comp _
  have hg₂ : g ≫ pullback.snd _ _ = 𝟙 _ := by
    rw [hg, Category.assoc, pullbackMap_snd, graph_snd]
    rfl
  have hz : g.base y ∈ G.sheet G.topOver h⁻¹ := by
    refine Scheme.Hom.mem_agreeLocus_of_comp_eq _ _ _ _ g ?_ y
    show g ≫ (pullback.fst _ _ ≫ 𝟙 _) ≫ G.act h⁻¹ = g ≫ pullback.snd _ _
    rw [Category.comp_id, ← Category.assoc, hg₁, hg₂, ← G.act_mul, inv_mul_cancel, G.act_one]
  have hfst : (pullback.fst G.topOver.left.hom G.cover.hom).base (g.base y) =
      (G.act h).base y := by
    rw [← hg₁]
    rfl
  have key := G.apply_eq_of_mem_sheet (T := G.topOver) (f := f.1) f.2 hz
  rw [hfst] at key
  have hL : G.restrictGraph Λ N ρ G.topOver
      (((G.descentPresheaf Λ N ρ).map (G.actHom h).op).hom f) y = f.1 (g.base y) := by
    rw [hg, Scheme.Hom.comp_apply]
    rfl
  have hR : G.restrictGraph Λ N ρ G.topOver f ((G.act h).base y) =
      f.1 ((G.graph G.topOver).base ((G.act h).base y)) := rfl
  rw [hL, key, hR]

end Action

section FiniteType

variable (Λ : Type r) [Ring Λ] (N : Type (max (u + 1) v)) [AddCommGroup N] [Module Λ N]
  (ρ : H →* Module.End Λ N)

/-- **The descent sheaf of a finitely generated module is finite type locally constant**: it is
constant on the covering, which pulls back to a covering of every étale `X`-scheme. -/
theorem isFiniteTypeLocallyConstant_descentSheaf [Module.Finite Λ N] :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology
      (G.descentSheaf Λ N ρ) := by
  intro W
  refine ⟨PUnit.{u + 2}, fun _ ↦ G.fiberObj W, fun _ ↦ G.fiberObjFst W,
    G.ofArrows_fiberObjFst_mem W, fun _ ↦ ⟨ModuleCat.of Λ N, ?_, ⟨?_⟩⟩⟩
  · show Module.Finite Λ N
    infer_instance
  · exact Stacks.ConstantSheaf.Localization.overPullbackIsoOfMap X.smallEtaleTopology
      (ModuleCat.{max (u + 1) v} Λ) (G.fiberObjSnd W) (G.descentSheaf Λ N ρ) _
      (G.trivialization Λ N ρ)

end FiniteType

end EtaleGaloisCovering

/-! ### The sections of a descent sheaf over the covering -/

section DescentSections

variable {Λ : Type r} [Ring Λ]

/-- A constant locally constant map on a connected nonempty space is determined by its value. -/
def constLinearEquiv (Y : Type*) [TopologicalSpace Y] [ConnectedSpace Y] (V : Type*)
    [AddCommGroup V] [Module Λ V] : V ≃ₗ[Λ] LocallyConstant Y V :=
  LinearEquiv.ofBijective (LocallyConstant.constₗ Λ)
    ⟨fun a b h ↦ by
      obtain ⟨y⟩ := (inferInstance : Nonempty Y)
      exact congrArg (fun f : LocallyConstant Y V ↦ f y) h,
     fun f ↦ by
      obtain ⟨y⟩ := (inferInstance : Nonempty Y)
      exact ⟨f y, (LocallyConstant.eq_const f y).symm⟩⟩

namespace EtaleGaloisCovering

variable {X : Scheme.{u}} {H : Type w} [Group H] (G : EtaleGaloisCovering X H)
  [ConnectedSpace G.cover.left] (N : Type v) [AddCommGroup N] [Module Λ N]
  (ρ : H →* Module.End Λ N)

/-- **The sections of the descent sheaf `D(N)` over a connected covering are `N`**: an
equivariant map on `A ×_X A` is its restriction to the diagonal, which is constant. -/
def descentSectionsEquiv : (G.descentPresheaf Λ N ρ).obj (op G.cover) ≃ₗ[Λ] N :=
  have : ConnectedSpace G.topOver.left.left := ‹ConnectedSpace G.cover.left›
  (LinearEquiv.ofBijective (G.restrictGraph Λ N ρ G.topOver)
    (G.bijective_restrictGraph Λ N ρ G.topOver)).trans
    (constLinearEquiv G.topOver.left.left N).symm

/-- **On the sections of `D(N)` over the covering, the automorphism `h` acts through
`ρ(h⁻¹)`.** -/
theorem descentSectionsEquiv_map_actHom (h : H)
    (d : (G.descentPresheaf Λ N ρ).obj (op G.cover)) :
    G.descentSectionsEquiv N ρ (((G.descentPresheaf Λ N ρ).map (G.actHom h).op).hom d) =
      ρ h⁻¹ (G.descentSectionsEquiv N ρ d) := by
  have : ConnectedSpace G.topOver.left.left := ‹ConnectedSpace G.cover.left›
  let c := constLinearEquiv (Λ := Λ) G.topOver.left.left N
  have hres : ∀ d', G.restrictGraph Λ N ρ G.topOver d' = c (G.descentSectionsEquiv N ρ d') :=
    fun d' ↦ (c.apply_symm_apply _).symm
  apply c.injective
  refine (hres _).symm.trans (LocallyConstant.ext fun y ↦ ?_)
  refine (G.restrictGraph_top_map_actHom h d y).trans ?_
  exact congrArg (ρ h⁻¹)
    (congrArg (fun f : LocallyConstant G.topOver.left.left N ↦ f ((G.act h).base y)) (hres d))

end EtaleGaloisCovering

end DescentSections

/-! ### Automorphisms of a pointed Galois cover come from the fundamental group -/

section Galois

variable {X : Scheme.{u}} [ConnectedSpace X] {x : GeometricPoint X}

/-- **Every automorphism of a pointed Galois cover is `τ_A(σ)` for some `σ ∈ π₁`.** -/
theorem surjective_galoisAut (A : PointedGaloisCover x) :
    Function.Surjective (fun σ : EtaleFundamentalGroup X x ↦ galoisAut x σ A) := by
  intro τ
  obtain ⟨ξ, hξ⟩ := AutGalois.π_surjective (finiteEtaleFiberFintypeFunctor X x) A τ
  refine ⟨autMulEquivEtaleFundamentalGroup X x
    ((autMulEquivAutGalois (finiteEtaleFiberFintypeFunctor X x)).symm (MulOpposite.op ξ)), ?_⟩
  simp only [galoisAut, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply,
    MulOpposite.unop_op]
  exact hξ

/-- `τ_A(σ⁻¹)` is the inverse of `τ_A(σ)`. -/
theorem galoisAut_inv (σ : EtaleFundamentalGroup X x) (A : PointedGaloisCover x) :
    galoisAut x σ⁻¹ A = (galoisAut x σ A)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← galoisAut_mul, mul_inv_cancel, galoisAut_one]

end Galois

/-! ### Representations of the fundamental group factoring through a pointed Galois cover -/

section AutRepresentation

variable {X : Scheme.{u}} [ConnectedSpace X] {x : GeometricPoint X} {M : Type*} [Monoid M]
  (A : PointedGaloisCover x) (ρ : EtaleFundamentalGroup X x →* M)
  (hρ : ∀ σ, galoisAut x σ A = 1 → ρ σ = 1)

include hρ in
/-- A representation of `π₁` trivial on the elements acting trivially on `A` takes the same
value on two elements inducing the same automorphism of `A`. -/
theorem eq_of_galoisAut_eq {a b : EtaleFundamentalGroup X x}
    (hab : galoisAut x a A = galoisAut x b A) : ρ a = ρ b := by
  have h1 : galoisAut x (b * a⁻¹) A = 1 := by
    rw [galoisAut_mul, galoisAut_inv, hab, inv_mul_cancel]
  calc ρ a = ρ (b * a⁻¹) * ρ a := by rw [hρ _ h1, one_mul]
    _ = ρ b := by rw [← map_mul, inv_mul_cancel_right]

/-- **A representation of `π₁` trivial on the elements acting trivially on a pointed Galois
cover `A` is a representation of `Aut(A)`**, through `τ_A(σ) ↦ ρ(σ⁻¹)`; the inverse makes the
anti-homomorphism `σ ↦ τ_A(σ)` into a homomorphism. -/
def autRepresentation : Aut A.obj →* M where
  toFun τ := ρ (surjective_galoisAut A τ).choose⁻¹
  map_one' := by
    have h := (surjective_galoisAut A 1).choose_spec
    simp only at h
    refine hρ _ ?_
    rw [galoisAut_inv, h, inv_one]
  map_mul' τ₁ τ₂ := by
    have h₁ := (surjective_galoisAut A τ₁).choose_spec
    have h₂ := (surjective_galoisAut A τ₂).choose_spec
    have h₁₂ := (surjective_galoisAut A (τ₁ * τ₂)).choose_spec
    simp only at h₁ h₂ h₁₂
    rw [← map_mul]
    refine eq_of_galoisAut_eq A ρ hρ ?_
    rw [galoisAut_mul, galoisAut_inv, galoisAut_inv, galoisAut_inv, h₁, h₂, h₁₂, mul_inv_rev]

/-- The representation of `Aut(A)` sends the image `τ_A(σ)` of `σ ∈ π₁` to `ρ(σ⁻¹)`. -/
theorem autRepresentation_galoisAut (σ : EtaleFundamentalGroup X x) :
    autRepresentation A ρ hρ (galoisAut x σ A) = ρ σ⁻¹ := by
  have h := (surjective_galoisAut A (galoisAut x σ A)).choose_spec
  simp only at h
  show ρ (surjective_galoisAut A (galoisAut x σ A)).choose⁻¹ = ρ σ⁻¹
  refine eq_of_galoisAut_eq A ρ hρ ?_
  rw [galoisAut_inv, galoisAut_inv, h]

end AutRepresentation

/-! ### Sheaves trivialized by a pointed Galois cover -/

section Trivialization

variable {X : Scheme.{u}} [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
  {x : GeometricPoint X} {Λ : Type r} [Ring Λ]

/-- A trivialization of a sheaf of `Λ`-modules `F`, with value `M`, over a pointed Galois cover
`A`: an isomorphism of the constant sheaf `M̲` with the restriction of `F` to `A`. -/
@[sga "4½ Rapport 5.12" "partial"]
abbrev GaloisTrivialization (A : PointedGaloisCover x)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
    (M : ModuleCat.{max (u + 1) r} Λ) : Type _ :=
  (constantSheaf (X.smallEtaleTopology.over ((PointedGaloisCover.toEtale x).obj A))
      (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
    (X.smallEtaleTopology.overPullback _ ((PointedGaloisCover.toEtale x).obj A)).obj F

variable {A : PointedGaloisCover x}
  {F F' : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
  {M M' : ModuleCat.{max (u + 1) r} Λ}

/-- A trivialization over `A` restricts to a trivialization over any pointed Galois cover
mapping to `A`, with the same value. -/
def GaloisTrivialization.ofHom {B : PointedGaloisCover x} (f : B ⟶ A)
    (e : GaloisTrivialization A F M) : GaloisTrivialization B F M :=
  Stacks.ConstantSheaf.Localization.overPullbackIsoOfMap X.smallEtaleTopology
    (ModuleCat.{max (u + 1) r} Λ) ((PointedGaloisCover.toEtale x).map f) F M e

include hX
/-- **The sections over `A` of a sheaf trivialized over `A` with value `M` are `M`.** -/
theorem GaloisTrivialization.bijective_sections (e : GaloisTrivialization A F M) :
    Function.Bijective ((toSheafify (X.smallEtaleTopology.over
        ((PointedGaloisCover.toEtale x).obj A))
      ((Functor.const (Over ((PointedGaloisCover.toEtale x).obj A))ᵒᵖ).obj M)).app
        (op (Over.mk (𝟙 _))) ≫ e.hom.hom.app (op (Over.mk (𝟙 _)))) := by
  have : IrreducibleSpace (Over.mk (𝟙 ((PointedGaloisCover.toEtale x).obj A))).left.left :=
    A.irreducibleSpace hX
  have h₁ := bijective_toSheafify_over_const_app Λ M
    (Over.mk (𝟙 ((PointedGaloisCover.toEtale x).obj A)))
  have h₂ : Function.Bijective (e.hom.hom.app (op (Over.mk (𝟙 _)))) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  exact h₂.comp h₁

/-- The identification of the sections over `A` with the value of a trivialization. -/
def GaloisTrivialization.sectionsEquiv (e : GaloisTrivialization A F M) :
    M ≃ₗ[Λ] F.obj.obj (op ((PointedGaloisCover.toEtale x).obj A)) :=
  LinearEquiv.ofBijective (((toSheafify (X.smallEtaleTopology.over
      ((PointedGaloisCover.toEtale x).obj A))
      ((Functor.const (Over ((PointedGaloisCover.toEtale x).obj A))ᵒᵖ).obj M)).app
        (op (Over.mk (𝟙 _))) ≫ e.hom.hom.app (op (Over.mk (𝟙 _)))).hom)
    (e.bijective_sections hX)

/-- The identification of the sections over `A` with the monodromy module. -/
def GaloisTrivialization.monodromyEquiv (e : GaloisTrivialization A F M) :
    F.obj.obj (op ((PointedGaloisCover.toEtale x).obj A)) ≃ₗ[Λ]
      ((monodromyAction x).obj F.obj).V :=
  LinearEquiv.ofBijective (colimit.ι ((monodromyDiagram x).obj F.obj) (op A)).hom
    (bijective_colimit_ι_monodromyDiagram hX e)

/-- `GaloisTrivialization.monodromyEquiv` is the colimit inclusion at `A`. -/
@[simp]
theorem GaloisTrivialization.monodromyEquiv_apply (e : GaloisTrivialization A F M)
    (s : F.obj.obj (op ((PointedGaloisCover.toEtale x).obj A))) :
    e.monodromyEquiv hX s = colimit.ι ((monodromyDiagram x).obj F.obj) (op A) s :=
  rfl

/-- **The monodromy module of a sheaf trivialized by a pointed Galois cover with a finitely
generated value is finitely generated.** -/
theorem GaloisTrivialization.finite_monodromy (e : GaloisTrivialization A F M)
    [Module.Finite Λ M] : Module.Finite Λ ((monodromyAction x).obj F.obj).V :=
  Module.Finite.equiv ((e.sectionsEquiv hX).trans (e.monodromyEquiv hX))

/-- **Faithfulness of the monodromy functor on sheaves trivialized by a common pointed Galois
cover.** -/
theorem GaloisTrivialization.hom_ext (e : GaloisTrivialization A F M)
    (e' : GaloisTrivialization A F' M') {φ ψ : F ⟶ F'}
    (h : (monodromyAction x).map φ.hom = (monodromyAction x).map ψ.hom) : φ = ψ := by
  refine (A.etaleGaloisCovering hX).hom_ext e ?_
  ext s
  apply (e'.monodromyEquiv hX).injective
  have h1 := ConcreteCategory.congr_hom (monodromyAction_map_ι φ.hom (op A)) s
  have h2 := ConcreteCategory.congr_hom (monodromyAction_map_ι ψ.hom (op A)) s
  rw [h] at h1
  exact h1.symm.trans h2

/-- **Fullness of the monodromy functor on sheaves trivialized by a common pointed Galois
cover.** -/
theorem GaloisTrivialization.exists_hom (e : GaloisTrivialization A F M)
    (e' : GaloisTrivialization A F' M')
    (g : (monodromyAction x).obj F.obj ⟶ (monodromyAction x).obj F'.obj) :
    ∃ φ : F ⟶ F', (monodromyAction x).map φ.hom = g := by
  let G := A.etaleGaloisCovering hX
  let ι := e.monodromyEquiv hX
  let ι' := e'.monodromyEquiv hX
  let f : F.obj.obj (op G.cover) ⟶ F'.obj.obj (op G.cover) :=
    ModuleCat.ofHom (ι'.symm.toLinearMap ∘ₗ g.hom.hom ∘ₗ ι.toLinearMap)
  have hfι : ∀ s, ι' (f s) = g.hom (ι s) := fun s ↦ ι'.apply_symm_apply _
  have hf : ∀ τ : Aut A.obj, F.obj.map (G.actHom τ).op ≫ f = f ≫ F'.obj.map (G.actHom τ).op := by
    intro τ
    obtain ⟨σ, rfl⟩ := surjective_galoisAut A τ
    let m := (finiteEtaleToEtale X).map (galoisAutHom x σ A)
    ext s
    have hρ : (((monodromyAction x).obj F.obj).ρ σ).asHom.hom (ι s) = ι (F.obj.map m.op s) :=
      monodromyAction_ρ_ι_apply F.obj σ (op A) s
    have hρ' : (((monodromyAction x).obj F'.obj).ρ σ).asHom.hom (ι' (f s)) =
        ι' (F'.obj.map m.op (f s)) :=
      monodromyAction_ρ_ι_apply F'.obj σ (op A) (f s)
    have hcomm : g.hom ((((monodromyAction x).obj F.obj).ρ σ).asHom.hom (ι s)) =
        (((monodromyAction x).obj F'.obj).ρ σ).asHom.hom (g.hom (ι s)) :=
      ConcreteCategory.congr_hom (g.comm σ) (ι s)
    have key : ι' (f (F.obj.map m.op s)) = ι' (F'.obj.map m.op (f s)) := by
      refine (hfι _).trans ?_
      rw [← hρ, hcomm, ← hfι, hρ']
    exact ι'.injective key
  obtain ⟨φ, hφ⟩ := G.exists_hom_app_cover_eq e f hf
  refine ⟨φ, ?_⟩
  apply Action.hom_ext
  ext v
  obtain ⟨s, rfl⟩ := ι.surjective v
  have h1 : ((monodromyAction x).map φ.hom).hom (ι s) = ι' (φ.hom.app (op G.cover) s) :=
    ConcreteCategory.congr_hom (monodromyAction_map_ι φ.hom (op A)) s
  exact h1.trans ((congrArg (fun k ↦ ι' (k s)) hφ).trans (hfι s))

end Trivialization

/-! ### Every finite continuous module is a monodromy module -/

section EssSurj

open Stacks.GroupCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

variable {X : Scheme.{u}} [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
  {x : GeometricPoint X} {Λ : Type r} [Ring Λ]

/-- The representation of `π₁` on a `Λ`-module with a `π₁`-action, by linear endomorphisms. -/
def actionLinearRepr (N : Action (ModuleCat.{max (u + 1) r} Λ) (EtaleFundamentalGroup X x)) :
    EtaleFundamentalGroup X x →* Module.End Λ N.V :=
  (ModuleCat.endRingEquiv N.V).toMonoidHom.comp N.ρ

variable (A : PointedGaloisCover x) (N : Action (ModuleCat.{max (u + 1) r} Λ)
    (EtaleFundamentalGroup X x))
  (hN : ∀ σ, galoisAut x σ A = 1 → actionLinearRepr N σ = 1)

/-- The descent sheaf along a pointed Galois cover `A` attached to a `Λ`-module with a
`π₁`-action trivial on the elements acting trivially on `A`. -/
abbrev monodromyDescentSheaf : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) :=
  (A.etaleGaloisCovering hX).descentSheaf Λ N.V (autRepresentation A (actionLinearRepr N) hN)

/-- The sections of the descent sheaf over the covering, identified with the module. -/
def monodromyDescentSectionsEquiv :
    (monodromyDescentSheaf hX A N hN).obj.obj (op ((PointedGaloisCover.toEtale x).obj A)) ≃ₗ[Λ]
      N.V :=
  have : ConnectedSpace (A.etaleGaloisCovering hX).cover.left := A.connectedSpace
  (A.etaleGaloisCovering hX).descentSectionsEquiv N.V
    (autRepresentation A (actionLinearRepr N) hN)

/-- **The descent sheaf intertwines the actions**: under the identification of its sections over
`A` with `N`, the action of `τ_A(σ)` is the action of `σ` on `N`. -/
theorem monodromyDescentSectionsEquiv_map (σ : EtaleFundamentalGroup X x)
    (d : (monodromyDescentSheaf hX A N hN).obj.obj (op ((PointedGaloisCover.toEtale x).obj A))) :
    monodromyDescentSectionsEquiv hX A N hN
        ((monodromyDescentSheaf hX A N hN).obj.map
          ((finiteEtaleToEtale X).map (galoisAutHom x σ A)).op d) =
      actionLinearRepr N σ (monodromyDescentSectionsEquiv hX A N hN d) := by
  have : ConnectedSpace (A.etaleGaloisCovering hX).cover.left := A.connectedSpace
  refine ((A.etaleGaloisCovering hX).descentSectionsEquiv_map_actHom N.V
    (autRepresentation A (actionLinearRepr N) hN) (galoisAut x σ A) d).trans ?_
  show autRepresentation A (actionLinearRepr N) hN (galoisAut x σ A)⁻¹
      (monodromyDescentSectionsEquiv hX A N hN d) =
    actionLinearRepr N σ (monodromyDescentSectionsEquiv hX A N hN d)
  rw [← galoisAut_inv, autRepresentation_galoisAut, inv_inv]

end EssSurj

/-! ### The equivalence, given trivializations by pointed Galois covers -/

section Equivalence

open Stacks.GroupCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

variable (X : Scheme.{u}) [IrreducibleSpace X] (x : GeometricPoint X) (Λ : Type r) [Ring Λ]

/-- Finite type local constancy, as a property of sheaves of `Λ`-modules on the small étale
site of `X`. -/
abbrev ftlcProperty : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) :=
  Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology

/-- The statement that every finite type locally constant sheaf of `Λ`-modules is trivialized,
with finitely generated value, by a pointed Galois cover. -/
abbrev TrivializedByPointedGaloisCovers : Prop :=
  ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ), ftlcProperty X Λ F →
    ∃ (A : PointedGaloisCover x) (M : ModuleCat.{max (u + 1) r} Λ),
      Module.Finite Λ M ∧ Nonempty (GaloisTrivialization A F M)

variable {X x Λ} (hX : IsGeometricallyUnibranch X) (htriv : TrivializedByPointedGaloisCovers X x Λ)

include htriv in
/-- Two finite type locally constant sheaves are trivialized by a common pointed Galois cover. -/
theorem exists_common_galoisTrivialization
    {F F' : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)} (hF : ftlcProperty X Λ F)
    (hF' : ftlcProperty X Λ F') :
    ∃ (A : PointedGaloisCover x) (M M' : ModuleCat.{max (u + 1) r} Λ),
      Nonempty (GaloisTrivialization A F M) ∧ Nonempty (GaloisTrivialization A F' M') := by
  obtain ⟨A₁, M, -, ⟨e⟩⟩ := htriv F hF
  obtain ⟨A₂, M', -, ⟨e'⟩⟩ := htriv F' hF'
  exact ⟨IsCofiltered.min A₁ A₂, M, M', ⟨e.ofHom (IsCofiltered.minToLeft A₁ A₂)⟩,
    ⟨e'.ofHom (IsCofiltered.minToRight A₁ A₂)⟩⟩

/-- **The monodromy functor on finite type locally constant sheaves**, landing in the finite
`Λ`-modules with a continuous `π₁`-action. -/
def monodromyFTLCFunctor : (ftlcProperty X Λ).FullSubcategory ⥤
    FiniteTypeContinuousModule.{r, u + 1, max (u + 1) r} Λ (EtaleFundamentalGroup X x) :=
  ObjectProperty.lift _ ((ftlcProperty X Λ).ι ⋙ sheafToPresheaf _ _ ⋙ monodromyModule x Λ)
    (fun F ↦ by
      obtain ⟨A, M, hM, ⟨e⟩⟩ := htriv F.obj F.property
      exact e.finite_monodromy hX)

/-- The monodromy functor on finite type locally constant sheaves is faithful. -/
instance : (monodromyFTLCFunctor hX htriv).Faithful where
  map_injective {F F'} φ ψ h := by
    obtain ⟨A, M, M', ⟨e⟩, ⟨e'⟩⟩ := exists_common_galoisTrivialization htriv F.property F'.property
    apply ObjectProperty.hom_ext
    exact GaloisTrivialization.hom_ext hX e e' (congrArg (fun k ↦ k.hom.hom.hom) h)

/-- The monodromy functor on finite type locally constant sheaves is full. -/
instance : (monodromyFTLCFunctor hX htriv).Full where
  map_surjective {F F'} g := by
    obtain ⟨A, M, M', ⟨e⟩, ⟨e'⟩⟩ := exists_common_galoisTrivialization htriv F.property F'.property
    obtain ⟨φ, hφ⟩ := GaloisTrivialization.exists_hom hX e e' g.hom.hom.hom
    refine ⟨ObjectProperty.homMk φ, ?_⟩
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact hφ

/-- Every finite `Λ`-module with a continuous `π₁(X, x)`-action is isomorphic to the monodromy
module of a finite type locally constant sheaf, the descent sheaf along a pointed Galois cover
on which the action is trivial. -/
instance : (monodromyFTLCFunctor hX htriv).EssSurj where
  mem_essImage N := by
    obtain ⟨K, -, hKo, hK⟩ :=
      exists_isOpen_normal_subgroup_ρ_eq_one_finiteType Λ (EtaleFundamentalGroup X x) N
    obtain ⟨A, hA⟩ := exists_pointedGaloisCover_subset x (hKo.mem_nhds K.one_mem)
    let N₀ := N.obj.obj.obj
    have hN : ∀ σ, galoisAut x σ A = 1 → actionLinearRepr N₀ σ = 1 := fun σ hσ ↦ by
      have h1 : N₀.ρ σ = 1 := hK σ (hA hσ)
      change ModuleCat.Hom.hom (N₀.ρ σ).asHom = 1
      rw [h1]
      rfl
    have : Module.Finite Λ N₀.V := N.property
    let D := monodromyDescentSheaf hX A N₀ hN
    have hD : ftlcProperty X Λ D :=
      (A.etaleGaloisCovering hX).isFiniteTypeLocallyConstant_descentSheaf Λ N₀.V _
    let e : GaloisTrivialization A D (ModuleCat.of Λ N₀.V) :=
      (A.etaleGaloisCovering hX).trivialization Λ N₀.V _
    let E := (e.monodromyEquiv hX).symm.trans (monodromyDescentSectionsEquiv hX A N₀ hN)
    refine ⟨⟨D, hD⟩, ⟨ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      (Action.mkIso E.toModuleIso fun σ ↦ ?_)))⟩⟩
    refine ModuleCat.hom_ext (LinearMap.ext fun v ↦ ?_)
    obtain ⟨d, rfl⟩ := (e.monodromyEquiv hX).surjective v
    have h1 : (((monodromyAction x).obj D.obj).ρ σ).asHom.hom (e.monodromyEquiv hX d) =
        e.monodromyEquiv hX
          (D.obj.map ((finiteEtaleToEtale X).map (galoisAutHom x σ A)).op d) :=
      monodromyAction_ρ_ι_apply D.obj σ (op A) d
    change E ((((monodromyAction x).obj D.obj).ρ σ).asHom.hom (e.monodromyEquiv hX d)) =
      (N₀.ρ σ).asHom.hom (E (e.monodromyEquiv hX d))
    rw [h1]
    change monodromyDescentSectionsEquiv hX A N₀ hN ((e.monodromyEquiv hX).symm
        (e.monodromyEquiv hX _)) =
      (N₀.ρ σ).asHom.hom (monodromyDescentSectionsEquiv hX A N₀ hN ((e.monodromyEquiv hX).symm
        (e.monodromyEquiv hX d)))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact monodromyDescentSectionsEquiv_map hX A N₀ hN σ d

/-- The monodromy functor on finite type locally constant sheaves is an equivalence. -/
instance : (monodromyFTLCFunctor hX htriv).IsEquivalence where

/-- **The finite type locally constant sheaves of `Λ`-modules are equivalent to the finite
`Λ`-modules with a continuous `π₁(X, x)`-action**, given that every finite type locally constant
sheaf is trivialized by a pointed Galois cover. -/
def monodromyFTLCEquivalence : (ftlcProperty X Λ).FullSubcategory ≌
    FiniteTypeContinuousModule.{r, u + 1, max (u + 1) r} Λ (EtaleFundamentalGroup X x) :=
  (monodromyFTLCFunctor hX htriv).asEquivalence

end Equivalence

end AlgebraicGeometry

end
