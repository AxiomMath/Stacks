module

public import StacksFrontier.Topology.Sheaves.Functors.Module.PresheafAdjunctionOverPushforward
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackPresheaf
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 008V — the explicit left adjoint `O ⊗_{p, f_p f_*O} f_p (-)` of `f_*`

Stacks 008V is about the explicit functor `G ↦ O ⊗_{p, f_p f_*O} f_p G`: take the presheaf
pullback `f_p G` (a presheaf of `f_p f_*O`-modules by Stacks 008T) and tensor it up to `O`
sectionwise along the counit `c_O : f_p f_*O ⟶ O`. Below this functor is built by hand,
`(O ⊗_{p, f_p f_*O} f_p G)(U) = O(U) ⊗_{(f_p f_*O)(U)} (f_p G)(U)`, and the bijection
`Mor(O ⊗_{p, f_p f_*O} f_p G, F) ≃ Mor(G, f_*F)` is proved as in Stacks, as the composite of
the tensor-restriction bijection (Stacks 006R) and the module form of the `f_p ⊣ f_*`
adjunction (Stacks 008U), whose module-compatibility is checked on germs. -/

@[expose] public section

universe u

open CategoryTheory

namespace Stacks.PresheafOfModules.TensorPullback

open TopologicalSpace Limits Opposite TensorProduct
open Stacks.PresheafOfModules.Pullback

section Germs

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The germ of `a ∈ O'(V)` at an index `c = (V, f⁻¹V ⊇ U)` of `N(U)`, read in `(f_p O')(U)`,
is the restriction to `U` of the unit image of `a` in `(f_p O')(f⁻¹V)`. -/
theorem pbRingIso_hom_ι (O' : TopCat.Presheaf RingCat.{u} Y) (U : (Opens X)ᵒᵖ)
    (c : ((CostructuredArrow (Opens.map f).op U)ᵒᵖ)ᵒᵖ) (a : O'.obj c.unop.unop.left) :
    (pbRingIso f O' U).hom (colimit.ι (pbRdiag f O' U) c a)
      = (pullbackRing f O').map c.unop.unop.hom (pullbackRingUnit f O' c.unop.unop.left a) := by
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  have hmor :
      colimit.ι ((opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor ⋙
          (CostructuredArrow.proj (Opens.map f).op U ⋙ O')) c ≫
        ((Functor.Final.colimitIso
            (opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor
            (CostructuredArrow.proj (Opens.map f).op U ⋙ O')).hom ≫
          ((Opens.map f).op.leftKanExtensionObjIsoColimit O' U).inv)
      = ((Opens.map f).op.leftKanExtensionUnit O').app c.unop.unop.left ≫
          ((Opens.map f).op.leftKanExtension O').map c.unop.unop.hom := by
    rw [← Category.assoc, Functor.Final.ι_colimitIso_hom]
    exact Functor.ι_leftKanExtensionObjIsoColimit_inv _ _ _ _
  have h2 := ConcreteCategory.congr_hom hmor a
  simp only [ConcreteCategory.comp_apply] at h2
  rw [pbRingIso, pullbackRingUnit]
  exact h2

/-- The abelian-group analogue of `pbRingIso_hom_ι`. -/
theorem pbAbIso_hom_ι (O' : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O')
    (U : (Opens X)ᵒᵖ) (c : ((CostructuredArrow (Opens.map f).op U)ᵒᵖ)ᵒᵖ)
    (s : G.obj c.unop.unop.left) :
    (pbAbIso f O' G U).hom (colimit.ι (pbMmod f O' G U).presheaf c s)
      = (pullbackAb f (underlyingAb O' G)).map c.unop.unop.hom
          (pullbackAbUnit f (underlyingAb O' G) c.unop.unop.left s) := by
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  have hmor :
      colimit.ι ((opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor ⋙
          (CostructuredArrow.proj (Opens.map f).op U ⋙ G.presheaf)) c ≫
        ((Functor.Final.colimitIso
            (opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor
            (CostructuredArrow.proj (Opens.map f).op U ⋙ G.presheaf)).hom ≫
          ((Opens.map f).op.leftKanExtensionObjIsoColimit G.presheaf U).inv)
      = ((Opens.map f).op.leftKanExtensionUnit G.presheaf).app c.unop.unop.left ≫
          ((Opens.map f).op.leftKanExtension G.presheaf).map c.unop.unop.hom := by
    rw [← Category.assoc, Functor.Final.ι_colimitIso_hom]
    exact Functor.ι_leftKanExtensionObjIsoColimit_inv _ _ _ _
  have h2 := ConcreteCategory.congr_hom hmor s
  rw [pbAbIso, pullbackAbUnit]
  exact h2

/-- **Joint germs.** A section `r` of `f_p O'` and a section `x` of `f_p G` over `U` are,
for a single open `V ⊆ Y` with `U ⊆ f⁻¹V`, the restrictions to `U` of the unit images of
some `a ∈ O'(V)` and `s ∈ G(V)`. -/
theorem exists_germ (O' : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O')
    (U : (Opens X)ᵒᵖ) (r : (pullbackRing f O').obj U)
    (x : (pullbackAb f (underlyingAb O' G)).obj U) :
    ∃ (V : (Opens Y)ᵒᵖ) (h : (Opens.map f).op.obj V ⟶ U) (a : O'.obj V) (s : G.obj V),
      r = (pullbackRing f O').map h (pullbackRingUnit f O' V a) ∧
      x = (pullbackAb f (underlyingAb O' G)).map h (pullbackAbUnit f (underlyingAb O' G) V s) := by
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  obtain ⟨c, a, s, ha, hs⟩ := PresheafOfModules.ModuleColimit.jointly_surjective₂
    (hcR := colimit.isColimit (pbRdiag f O' U))
    (hcM := colimit.isColimit (pbMmod f O' G U).presheaf)
    ((pbRingIso f O' U).inv r) ((pbAbIso f O' G U).inv x)
  refine ⟨c.unop.unop.left, c.unop.unop.hom, a, s, ?_, ?_⟩
  · refine Eq.trans ?_ (pbRingIso_hom_ι f O' U c a)
    change r = (pbRingIso f O' U).hom ((colimit.ι (pbRdiag f O' U) c).hom a)
    rw [show (colimit.ι (pbRdiag f O' U) c).hom a = (pbRingIso f O' U).inv r from ha]
    exact (Iso.inv_hom_id_apply (pbRingIso f O' U) r).symm
  · refine Eq.trans ?_ (pbAbIso_hom_ι f O' G U c s)
    change x = (pbAbIso f O' G U).hom ((colimit.ι (pbMmod f O' G U).presheaf c).hom s)
    rw [show (colimit.ι (pbMmod f O' G U).presheaf c).hom s = (pbAbIso f O' G U).inv x from hs]
    exact (Iso.inv_hom_id_apply (pbAbIso f O' G U) x).symm

/-- The sections of `f_p O'` commute when those of `O'` do: two sections are germs at a
common open, where they commute. -/
theorem pullbackRing_mul_comm (O' : TopCat.Presheaf RingCat.{u} Y)
    (hO' : ∀ V (a b : O'.obj V), a * b = b * a) (U : (Opens X)ᵒᵖ)
    (r₁ r₂ : (pullbackRing f O').obj U) : r₁ * r₂ = r₂ * r₁ := by
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  obtain ⟨c, a₁, a₂, -, h₁, h₂, -⟩ := PresheafOfModules.ModuleColimit.jointly_surjective₃
    (hcR := colimit.isColimit (pbRdiag f O' U))
    (hcM := colimit.isColimit (pbMmod f O' (PresheafOfModules.unit O') U).presheaf)
    ((pbRingIso f O' U).inv r₁) ((pbRingIso f O' U).inv r₂) 0
  have e : ∀ r : (pullbackRing f O').obj U, ∀ a,
      (colimit.ι (pbRdiag f O' U) c).hom a = (pbRingIso f O' U).inv r →
        r = (colimit.ι (pbRdiag f O' U) c ≫ (pbRingIso f O' U).hom).hom a := by
    intro r a h
    rw [RingCat.hom_comp, RingHom.comp_apply, h]
    exact (Iso.inv_hom_id_apply (pbRingIso f O' U) r).symm
  rw [e r₁ a₁ h₁, e r₂ a₂ h₂, ← map_mul, ← map_mul, hO']

end Germs

section Setting

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (O : TopCat.Presheaf CommRingCat.{u} X)

/-- The presheaf of rings `O` on `X`, as a presheaf valued in `RingCat`. -/
abbrev ringsX : TopCat.Presheaf RingCat.{u} X := O ⋙ forget₂ CommRingCat RingCat

/-- The presheaf of rings `f_*O` on `Y`. -/
abbrev ringsY : TopCat.Presheaf RingCat.{u} Y := pushforwardRings f (ringsX O)

/-- The presheaf of rings `f_p f_*O` on `X`. -/
noncomputable abbrev ringsPP : TopCat.Presheaf RingCat.{u} X := pullbackRing f (ringsY f O)

noncomputable instance (U : (Opens X)ᵒᵖ) : CommRing ((ringsX O).obj U) :=
  inferInstanceAs (CommRing (O.obj U))

noncomputable instance (U : (Opens X)ᵒᵖ) : CommRing ((ringsPP f O).obj U) :=
  @CommRing.mk _ (inferInstanceAs (Ring ((ringsPP f O).obj U)))
    (pullbackRing_mul_comm f (ringsY f O)
      (fun V a b => mul_comm (G := (O.obj ((Opens.map f).op.obj V))) a b) U)

/-- The counit `c_O : f_p f_*O ⟶ O` of the adjunction `f_p ⊣ f_*` on presheaves of rings. -/
noncomputable def counitRings : ringsPP f O ⟶ ringsX O :=
  (TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).counit.app (ringsX O)

/-- `O(U)` is a `(f_p f_*O)(U)`-algebra through `c_O`. -/
noncomputable instance (U : (Opens X)ᵒᵖ) : Algebra ((ringsPP f O).obj U) ((ringsX O).obj U) :=
  ((counitRings f O).app U).hom.toAlgebra

theorem smul_eq_counit_mul {U : (Opens X)ᵒᵖ} (r : (ringsPP f O).obj U) (b : (ringsX O).obj U) :
    r • b = ((counitRings f O).app U).hom r * b := rfl

theorem counitRings_naturality_apply {U V : (Opens X)ᵒᵖ} (g : U ⟶ V)
    (r : (ringsPP f O).obj U) :
    ((counitRings f O).app V).hom (((ringsPP f O).map g).hom r)
      = ((ringsX O).map g).hom (((counitRings f O).app U).hom r) :=
  NatTrans.naturality_apply (counitRings f O) g r

/-- The triangle identity: `c_O` sends the germ of `a ∈ (f_*O)(V)` over `f⁻¹V` to `a`. -/
theorem counitRings_unit (V : (Opens Y)ᵒᵖ) (a : (ringsY f O).obj V) :
    ((counitRings f O).app ((Opens.map f).op.obj V)).hom (pullbackRingUnit f (ringsY f O) V a)
      = a := by
  rw [pullbackRingUnit_eq_adjunction_unit]
  have := ConcreteCategory.congr_hom (NatTrans.congr_app
    ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).right_triangle_components
      (ringsX O)) V) a
  exact this

theorem ringsX_map_id (U : (Opens X)ᵒᵖ) (b : (ringsX O).obj U) :
    ((ringsX O).map (𝟙 U)).hom b = b := by
  rw [CategoryTheory.Functor.map_id]; rfl

theorem ringsX_map_comp {U V W : (Opens X)ᵒᵖ} (g : U ⟶ V) (h : V ⟶ W) (b : (ringsX O).obj U) :
    ((ringsX O).map (g ≫ h)).hom b = ((ringsX O).map h).hom (((ringsX O).map g).hom b) := by
  rw [CategoryTheory.Functor.map_comp]; rfl

/-- `f_p G`, the presheaf pullback of a presheaf of `f_*O`-modules, as a presheaf of
`f_p f_*O`-modules (Stacks 008T). -/
noncomputable abbrev pullbackObj (G : PresheafOfModules.{u} (ringsY f O)) :
    PresheafOfModules.{u} (ringsPP f O) :=
  (pullbackModuleFunctor f (ringsY f O)).obj G

theorem pullbackObj_restrict_id (G : PresheafOfModules.{u} (ringsY f O)) (U : (Opens X)ᵒᵖ)
    (x : (pullbackObj f O G).obj U) : (pullbackObj f O G).restrictₛₗ (𝟙 U) x = x := by
  change ((pullbackAb f (underlyingAb (ringsY f O) G)).map (𝟙 U)).hom x = x
  rw [CategoryTheory.Functor.map_id]; rfl

theorem pullbackObj_restrict_comp (G : PresheafOfModules.{u} (ringsY f O)) {U V W : (Opens X)ᵒᵖ}
    (g : U ⟶ V) (h : V ⟶ W) (x : (pullbackObj f O G).obj U) :
    (pullbackObj f O G).restrictₛₗ (g ≫ h) x
      = (pullbackObj f O G).restrictₛₗ h ((pullbackObj f O G).restrictₛₗ g x) := by
  change ((pullbackAb f (underlyingAb (ringsY f O) G)).map (g ≫ h)).hom x
    = ((pullbackAb f (underlyingAb (ringsY f O) G)).map h).hom
      (((pullbackAb f (underlyingAb (ringsY f O) G)).map g).hom x)
  rw [CategoryTheory.Functor.map_comp]; rfl

/-- The sections `O(U) ⊗_{(f_p f_*O)(U)} (f_p G)(U)` of `O ⊗_{p, f_p f_*O} f_p G`. -/
abbrev tensorSections (G : PresheafOfModules.{u} (ringsY f O)) (U : (Opens X)ᵒᵖ) : Type u :=
  (ringsX O).obj U ⊗[(ringsPP f O).obj U] (pullbackObj f O G).obj U

/-- The restriction maps of `O ⊗_{p, f_p f_*O} f_p G`: `b ⊗ x ↦ b|_V ⊗ x|_V`. -/
noncomputable def tensorRestrict (G : PresheafOfModules.{u} (ringsY f O)) {U V : (Opens X)ᵒᵖ}
    (g : U ⟶ V) : tensorSections f O G U →+ tensorSections f O G V :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
        (fun x => ((ringsX O).map g).hom b ⊗ₜ[(ringsPP f O).obj V]
          (pullbackObj f O G).restrictₛₗ g x)
        (fun x y => by rw [map_add, tmul_add]))
      (fun b b' => by
        ext x
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_tmul]))
    (fun r b x => by
      simp only [AddMonoidHom.mk'_apply]
      rw [LinearMap.map_smulₛₗ, ← smul_tmul, smul_eq_counit_mul, smul_eq_counit_mul,
        map_mul, counitRings_naturality_apply])

theorem tensorRestrict_tmul (G : PresheafOfModules.{u} (ringsY f O)) {U V : (Opens X)ᵒᵖ}
    (g : U ⟶ V) (b : (ringsX O).obj U) (x : (pullbackObj f O G).obj U) :
    tensorRestrict f O G g (b ⊗ₜ x)
      = ((ringsX O).map g).hom b ⊗ₜ (pullbackObj f O G).restrictₛₗ g x := rfl

theorem tensorRestrict_smul (G : PresheafOfModules.{u} (ringsY f O)) {U V : (Opens X)ᵒᵖ}
    (g : U ⟶ V) (b₀ : (ringsX O).obj U) (t : tensorSections f O G U) :
    tensorRestrict f O G g (b₀ • t) = ((ringsX O).map g).hom b₀ • tensorRestrict f O G g t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul b x => rw [smul_tmul', tensorRestrict_tmul, tensorRestrict_tmul, smul_tmul', smul_eq_mul,
      smul_eq_mul, map_mul]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

/-- The underlying presheaf of abelian groups of `O ⊗_{p, f_p f_*O} f_p G`. -/
noncomputable def tensorPresheaf (G : PresheafOfModules.{u} (ringsY f O)) :
    (Opens X)ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (tensorSections f O G U)
  map g := AddCommGrpCat.ofHom (tensorRestrict f O G g)
  map_id U := by
    ext t
    change tensorRestrict f O G (𝟙 U) t = t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul b x => rw [tensorRestrict_tmul, ringsX_map_id, pullbackObj_restrict_id]
    | add t t' ht ht' => rw [map_add, ht, ht']
  map_comp g h := by
    ext t
    change tensorRestrict f O G (g ≫ h) t = tensorRestrict f O G h (tensorRestrict f O G g t)
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul b x => rw [tensorRestrict_tmul, tensorRestrict_tmul, tensorRestrict_tmul,
        ringsX_map_comp, pullbackObj_restrict_comp]
    | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']

noncomputable instance (G : PresheafOfModules.{u} (ringsY f O)) (U : (Opens X)ᵒᵖ) :
    Module ((ringsX O).obj U) ((tensorPresheaf f O G).obj U) :=
  inferInstanceAs (Module ((ringsX O).obj U) (tensorSections f O G U))

/-- The presheaf of `O`-modules `O ⊗_{p, f_p f_*O} f_p G`, with sections
`O(U) ⊗_{(f_p f_*O)(U)} (f_p G)(U)`, the tensor product taken along `c_O`. -/
noncomputable def tensorObj (G : PresheafOfModules.{u} (ringsY f O)) :
    PresheafOfModules.{u} (ringsX O) :=
  PresheafOfModules.ofPresheaf (tensorPresheaf f O G)
    (fun _ _ g b t => tensorRestrict_smul f O G g b t)

/-- On a morphism `φ : G ⟶ G'`, the map `O(U) ⊗ (f_p G)(U) ⟶ O(U) ⊗ (f_p G')(U)` is
`id ⊗ f_p φ`. -/
noncomputable def tensorMapApp {G G' : PresheafOfModules.{u} (ringsY f O)} (φ : G ⟶ G')
    (U : (Opens X)ᵒᵖ) : tensorSections f O G U →ₗ[(ringsX O).obj U] tensorSections f O G' U :=
  (((pullbackModuleFunctor f (ringsY f O)).map φ).app U).hom.baseChange _

theorem tensorMapApp_tmul {G G' : PresheafOfModules.{u} (ringsY f O)} (φ : G ⟶ G')
    (U : (Opens X)ᵒᵖ) (b : (ringsX O).obj U) (x : (pullbackObj f O G).obj U) :
    tensorMapApp f O φ U (b ⊗ₜ x)
      = b ⊗ₜ (((pullbackModuleFunctor f (ringsY f O)).map φ).app U).hom x :=
  rfl

/-- **The functor `G ↦ O ⊗_{p, f_p f_*O} f_p G`** from presheaves of `f_*O`-modules on `Y` to
presheaves of `O`-modules on `X`: the presheaf pullback `f_p` (Stacks 008T) followed by the
sectionwise tensor product along the counit `c_O : f_p f_*O ⟶ O`. -/
noncomputable def tensorPullback :
    PresheafOfModules.{u} (ringsY f O) ⥤ PresheafOfModules.{u} (ringsX O) where
  obj G := tensorObj f O G
  map {G G'} φ := PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (tensorMapApp f O φ U).toAddMonoidHom
      naturality := fun U V g => by
        ext t
        change tensorMapApp f O φ V (tensorRestrict f O G g t)
          = tensorRestrict f O G' g (tensorMapApp f O φ U t)
        induction t using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero, map_zero, map_zero]
        | tmul b x =>
          rw [tensorRestrict_tmul, tensorMapApp_tmul, tensorMapApp_tmul, tensorRestrict_tmul]
          congr 1
          exact PresheafOfModules.naturality_apply _ g x
        | add t t' ht ht' => rw [map_add, map_add, map_add, map_add, ht, ht'] }
    (fun U b t => (tensorMapApp f O φ U).map_smul b t)
  map_id G := by
    refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    change tensorMapApp f O (𝟙 G) U t = t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul b x => rw [tensorMapApp_tmul, CategoryTheory.Functor.map_id]; rfl
    | add t t' ht ht' => rw [map_add, ht, ht']
  map_comp {G G' G''} φ ψ := by
    refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    change tensorMapApp f O (φ ≫ ψ) U t = tensorMapApp f O ψ U (tensorMapApp f O φ U t)
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul b x =>
      rw [tensorMapApp_tmul, tensorMapApp_tmul, tensorMapApp_tmul,
        CategoryTheory.Functor.map_comp]
      rfl
    | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']

/-! ### The bijection `Mor(O ⊗_{p, f_p f_*O} f_p G, F) ≃ Mor(G, f_*F)` -/

/-- The underlying additive maps `(f_p G)(U) ⟶ F(U)` of a morphism of presheaves of
`f_p f_*O`-modules `f_p G ⟶ F_{f_p f_*O}`. -/
noncomputable def restrictApp {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)}
    (φ : pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F)
    (U : (Opens X)ᵒᵖ) : (pullbackObj f O G).obj U →+ F.obj U :=
  (φ.app U).hom.toAddMonoidHom

theorem restrictApp_smul {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)}
    (φ : pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F)
    (U : (Opens X)ᵒᵖ) (r : (ringsPP f O).obj U) (x : (pullbackObj f O G).obj U) :
    restrictApp f O φ U (r • x) = ((counitRings f O).app U).hom r • restrictApp f O φ U x :=
  (φ.app U).hom.map_smul r x

theorem restrictApp_naturality {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)}
    (φ : pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F)
    {U V : (Opens X)ᵒᵖ} (g : U ⟶ V) (x : (pullbackObj f O G).obj U) :
    restrictApp f O φ V ((pullbackObj f O G).restrictₛₗ g x)
      = F.restrictₛₗ g (restrictApp f O φ U x) :=
  PresheafOfModules.naturality_apply φ g x

/-- The `O(U)`-linear extension `b ⊗ x ↦ b • φ(x)` of `φ : f_p G ⟶ F_{f_p f_*O}` to
`O(U) ⊗_{(f_p f_*O)(U)} (f_p G)(U)`. -/
noncomputable def tensorLift {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)}
    (φ : pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F)
    (U : (Opens X)ᵒᵖ) : tensorSections f O G U →+ F.obj U :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun x => b • restrictApp f O φ U x)
        (fun x y => by rw [map_add, smul_add]))
      (fun b b' => by
        ext x
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, add_smul]))
    (fun r b x => by
      simp only [AddMonoidHom.mk'_apply]
      rw [restrictApp_smul, smul_eq_counit_mul, mul_comm, mul_smul])

theorem tensorLift_tmul {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)}
    (φ : pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F)
    (U : (Opens X)ᵒᵖ) (b : (ringsX O).obj U) (x : (pullbackObj f O G).obj U) :
    tensorLift f O φ U (b ⊗ₜ x) = b • restrictApp f O φ U x := rfl

theorem tensorLift_smul {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)}
    (φ : pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F)
    (U : (Opens X)ᵒᵖ) (b₀ : (ringsX O).obj U) (t : tensorSections f O G U) :
    tensorLift f O φ U (b₀ • t) = b₀ • tensorLift f O φ U t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul b x => rw [smul_tmul', tensorLift_tmul, tensorLift_tmul, smul_eq_mul, mul_smul]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

theorem tensorLift_naturality {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)}
    (φ : pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F)
    {U V : (Opens X)ᵒᵖ} (g : U ⟶ V) (t : tensorSections f O G U) :
    tensorLift f O φ V (tensorRestrict f O G g t) = F.restrictₛₗ g (tensorLift f O φ U t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b x =>
    rw [tensorRestrict_tmul, tensorLift_tmul, tensorLift_tmul, restrictApp_naturality,
      LinearMap.map_smulₛₗ]
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add]

/-- The sectionwise linear maps of a morphism `Ψ : O ⊗_{p, f_p f_*O} f_p G ⟶ F`. -/
noncomputable def tensorHomApp {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (Ψ : tensorObj f O G ⟶ F) (U : (Opens X)ᵒᵖ) :
    tensorSections f O G U →ₗ[(ringsX O).obj U] F.obj U :=
  (Ψ.app U).hom

theorem tensorHomApp_naturality {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (Ψ : tensorObj f O G ⟶ F) {U V : (Opens X)ᵒᵖ}
    (g : U ⟶ V) (t : tensorSections f O G U) :
    tensorHomApp f O Ψ V (tensorRestrict f O G g t) = F.restrictₛₗ g (tensorHomApp f O Ψ U t) :=
  PresheafOfModules.naturality_apply Ψ g t

/-- **Stacks 006R for `c_O`.** The bijection
`Mor_{PMod(O)}(O ⊗_{p, f_p f_*O} f_p G, F) ≃ Mor_{PMod(f_p f_*O)}(f_p G, F_{f_p f_*O})`,
`Ψ ↦ (x ↦ Ψ(1 ⊗ x))`, with inverse `φ ↦ (b ⊗ x ↦ b • φ(x))`. -/
noncomputable def tensorHomEquiv (G : PresheafOfModules.{u} (ringsY f O))
    (F : PresheafOfModules.{u} (ringsX O)) :
    (tensorObj f O G ⟶ F) ≃
      (pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F) where
  toFun Ψ := PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun x => tensorHomApp f O Ψ U ((1 : (ringsX O).obj U) ⊗ₜ[(ringsPP f O).obj U] x))
        (fun x y => by rw [tmul_add]; exact map_add _ _ _))
      naturality := fun U V g => by
        refine AddCommGrpCat.ext fun (x : (pullbackObj f O G).obj U) => ?_
        change tensorHomApp f O Ψ V
            ((1 : (ringsX O).obj V) ⊗ₜ (pullbackObj f O G).restrictₛₗ g x)
          = F.restrictₛₗ g (tensorHomApp f O Ψ U ((1 : (ringsX O).obj U) ⊗ₜ x))
        have h := tensorHomApp_naturality f O Ψ g ((1 : (ringsX O).obj U) ⊗ₜ x)
        rw [tensorRestrict_tmul, map_one] at h
        exact h }
    (fun U r x => by
      change tensorHomApp f O Ψ U ((1 : (ringsX O).obj U) ⊗ₜ (r • x))
        = ((counitRings f O).app U).hom r • tensorHomApp f O Ψ U ((1 : (ringsX O).obj U) ⊗ₜ x)
      rw [← smul_tmul, smul_eq_counit_mul, mul_one, ← LinearMap.map_smul, smul_tmul',
        smul_eq_mul, mul_one])
  invFun φ := PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (tensorLift f O φ U)
      naturality := fun U V g => by
        ext t
        exact tensorLift_naturality f O φ g t }
    (fun U b t => tensorLift_smul f O φ U b t)
  left_inv Ψ := by
    refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    change tensorLift f O _ U t = tensorHomApp f O Ψ U t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul b x =>
      rw [tensorLift_tmul]
      change b • tensorHomApp f O Ψ U ((1 : (ringsX O).obj U) ⊗ₜ x) = _
      rw [← LinearMap.map_smul, smul_tmul', smul_eq_mul, mul_one]
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']
  right_inv φ := by
    refine PresheafOfModules.hom_ext fun U => ?_
    ext x
    change tensorLift f O φ U ((1 : (ringsX O).obj U) ⊗ₜ x) = restrictApp f O φ U x
    rw [tensorLift_tmul, one_smul]

theorem adjAb_homEquiv_app {G' : TopCat.Presheaf Ab.{u} Y} {F' : TopCat.Presheaf Ab.{u} X}
    (ψ : (TopCat.Presheaf.pullback Ab.{u} f).obj G' ⟶ F') (V : (Opens Y)ᵒᵖ) (s : G'.obj V) :
    (((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv G' F' ψ).app V) s
      = (ψ.app ((Opens.map f).op.obj V)) (pullbackAbUnit f G' V s) := by
  rw [Adjunction.homEquiv_unit, pullbackAbUnit_eq_adjunction_unit]
  rfl

/-- A morphism `ψ : f_p G' ⟶ F'` of presheaves of abelian groups, on the restriction to `U` of
the germ of `s ∈ G'(V)`, is the restriction of its adjoint `G' ⟶ f_*F'` at `s`. -/
theorem app_map_pullbackAbUnit {G' : TopCat.Presheaf Ab.{u} Y} {F' : TopCat.Presheaf Ab.{u} X}
    (ψ : (TopCat.Presheaf.pullback Ab.{u} f).obj G' ⟶ F') {U : (Opens X)ᵒᵖ} (V : (Opens Y)ᵒᵖ)
    (h : (Opens.map f).op.obj V ⟶ U) (s : G'.obj V) :
    (ψ.app U) (((pullbackAb f G').map h) (pullbackAbUnit f G' V s))
      = (F'.map h) ((((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv G' F'
          ψ).app V) s) := by
  rw [adjAb_homEquiv_app]
  exact NatTrans.naturality_apply ψ h _

/-- The underlying morphism `f_p G ⟶ F` of presheaves of abelian groups of a morphism
`f_p G ⟶ F_{f_p f_*O}` of presheaves of modules. -/
noncomputable def abHom {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)}
    (ψ : pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F) :
    (TopCat.Presheaf.pullback Ab.{u} f).obj (underlyingAb (ringsY f O) G) ⟶ F.presheaf :=
  (PresheafOfModules.toPresheaf _).map ψ

/-- The underlying morphism `G ⟶ f_*F` of presheaves of abelian groups of a morphism
`G ⟶ f_*F` of presheaves of `f_*O`-modules. -/
noncomputable def abHom' {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (φ : G ⟶ (pushforwardModules008V f (ringsX O)).obj F) :
    underlyingAb (ringsY f O) G ⟶ (TopCat.Presheaf.pushforward Ab.{u} f).obj F.presheaf :=
  (PresheafOfModules.toPresheaf _).map φ

/-- The underlying morphism of presheaves of abelian groups of `h : G' ⟶ G`. -/
noncomputable def abMap {G' G : PresheafOfModules.{u} (ringsY f O)} (h : G' ⟶ G) :
    underlyingAb (ringsY f O) G' ⟶ underlyingAb (ringsY f O) G :=
  (PresheafOfModules.toPresheaf _).map h

theorem abHom'_comp {G' G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (h : G' ⟶ G)
    (φ : G ⟶ (pushforwardModules008V f (ringsX O)).obj F) :
    abHom' f O (h ≫ φ) = abMap f O h ≫ abHom' f O φ := rfl

/-- A section `a` of `f_*O` over `V`, read as a section of `O` over `f⁻¹V`. -/
abbrev toX {V : (Opens Y)ᵒᵖ} (a : (ringsY f O).obj V) : (ringsX O).obj ((Opens.map f).op.obj V) :=
  a

theorem counitRings_unit' (V : (Opens Y)ᵒᵖ) (a : (ringsY f O).obj V) :
    ((counitRings f O).app ((Opens.map f).op.obj V)).hom (pullbackRingUnit f (ringsY f O) V a)
      = toX f O a :=
  counitRings_unit f O V a

/-- The germ map `G(V) ⟶ (f_p G)(f⁻¹V)`. -/
noncomputable def germ (G : PresheafOfModules.{u} (ringsY f O)) (V : (Opens Y)ᵒᵖ) :
    G.obj V →+ (pullbackObj f O G).obj ((Opens.map f).op.obj V) :=
  (pullbackAbUnit f (underlyingAb (ringsY f O) G) V).hom

theorem germ_smul (G : PresheafOfModules.{u} (ringsY f O)) (V : (Opens Y)ᵒᵖ)
    (a : (ringsY f O).obj V) (s : G.obj V) :
    germ f O G V (a • s) = pullbackRingUnit f (ringsY f O) V a • germ f O G V s :=
  pullbackModule_unit_smul f (ringsY f O) G V a s

theorem germ_naturality (G : PresheafOfModules.{u} (ringsY f O))
    {V V' : (Opens Y)ᵒᵖ} (g : V ⟶ V') (s : G.obj V) :
    germ f O G V' (G.map g s)
      = (pullbackObj f O G).restrictₛₗ ((Opens.map f).op.map g) (germ f O G V s) := by
  have := NatTrans.naturality_apply
    ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).unit.app
      (underlyingAb (ringsY f O) G)) g s
  rw [← pullbackAbUnit_eq_adjunction_unit, ← pullbackAbUnit_eq_adjunction_unit] at this
  exact this

theorem exists_germ' (G : PresheafOfModules.{u} (ringsY f O)) (U : (Opens X)ᵒᵖ)
    (r : (ringsPP f O).obj U) (x : (pullbackObj f O G).obj U) :
    ∃ (V : (Opens Y)ᵒᵖ) (h : (Opens.map f).op.obj V ⟶ U) (a : (ringsY f O).obj V) (s : G.obj V),
      r = ((ringsPP f O).map h).hom (pullbackRingUnit f (ringsY f O) V a) ∧
      x = (pullbackObj f O G).restrictₛₗ h (germ f O G V s) := by
  obtain ⟨V, h, a, s, hr, hx⟩ := exists_germ f (ringsY f O) G U r x
  exact ⟨V, h, a, s, hr, hx⟩

/-- The sectionwise additive maps `G(V) ⟶ F(f⁻¹V)` of `φ : G ⟶ f_*F`. -/
noncomputable def pushApp {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (φ : G ⟶ (pushforwardModules008V f (ringsX O)).obj F)
    (V : (Opens Y)ᵒᵖ) : G.obj V →+ F.obj ((Opens.map f).op.obj V) :=
  (φ.app V).hom.toAddMonoidHom

theorem pushApp_smul {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (φ : G ⟶ (pushforwardModules008V f (ringsX O)).obj F)
    (V : (Opens Y)ᵒᵖ) (a : (ringsY f O).obj V) (s : G.obj V) :
    pushApp f O φ V (a • s) = toX f O a • pushApp f O φ V s :=
  (φ.app V).hom.map_smul a s

/-- The sectionwise additive maps `(f_p G)(U) ⟶ F(U)` of the adjoint `f_p G ⟶ F` of
`φ : G ⟶ f_*F` under `f_p ⊣ f_*` on presheaves of abelian groups. -/
noncomputable def symmApp {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (φ : G ⟶ (pushforwardModules008V f (ringsX O)).obj F)
    (U : (Opens X)ᵒᵖ) : (pullbackObj f O G).obj U →+ F.obj U :=
  ((((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
    (underlyingAb (ringsY f O) G) F.presheaf).symm (abHom' f O φ)).app U).hom

theorem symmApp_germ {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (φ : G ⟶ (pushforwardModules008V f (ringsX O)).obj F)
    {U : (Opens X)ᵒᵖ} (V : (Opens Y)ᵒᵖ) (h : (Opens.map f).op.obj V ⟶ U) (s : G.obj V) :
    symmApp f O φ U ((pullbackObj f O G).restrictₛₗ h (germ f O G V s))
      = F.restrictₛₗ h (pushApp f O φ V s) := by
  have := app_map_pullbackAbUnit f
    (((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
      (underlyingAb (ringsY f O) G) F.presheaf).symm (abHom' f O φ)) V h s
  rw [Equiv.apply_symm_apply] at this
  exact this

theorem symmApp_smul {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (φ : G ⟶ (pushforwardModules008V f (ringsX O)).obj F)
    (U : (Opens X)ᵒᵖ) (r : (ringsPP f O).obj U) (x : (pullbackObj f O G).obj U) :
    symmApp f O φ U (r • x) = ((counitRings f O).app U).hom r • symmApp f O φ U x := by
  obtain ⟨V, h, a, s, rfl, rfl⟩ := exists_germ' f O G U r x
  rw [← LinearMap.map_smulₛₗ, ← germ_smul, symmApp_germ, symmApp_germ, pushApp_smul,
    LinearMap.map_smulₛₗ, counitRings_naturality_apply, counitRings_unit']

/-- The forward map of `pullbackHomEquiv` on sections over `V`: `s ↦ ψ(germ of s)`. -/
noncomputable def adjointApp {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)}
    (ψ : pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F)
    (V : (Opens Y)ᵒᵖ) :
    G.obj V →ₗ[(ringsY f O).obj V] ((pushforwardModules008V f (ringsX O)).obj F).obj V where
  toFun s := restrictApp f O ψ _ (germ f O G V s)
  map_add' s s' := by rw [map_add, map_add]; rfl
  map_smul' a s := by
    change restrictApp f O ψ _ (germ f O G V (a • s))
      = toX f O a • restrictApp f O ψ _ (germ f O G V s)
    rw [germ_smul, restrictApp_smul, counitRings_unit']

theorem symmApp_germ_self {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (φ : G ⟶ (pushforwardModules008V f (ringsX O)).obj F)
    (V : (Opens Y)ᵒᵖ) (s : G.obj V) :
    symmApp f O φ _ (germ f O G V s) = pushApp f O φ V s := by
  have := adjAb_homEquiv_app f
    (((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
      (underlyingAb (ringsY f O) G) F.presheaf).symm (abHom' f O φ)) V s
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

/-- The forward map of `pullbackHomEquiv`: `ψ ↦ (s ↦ ψ(germ of s))`. -/
noncomputable def adjointHom {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)}
    (ψ : pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F) :
    G ⟶ (pushforwardModules008V f (ringsX O)).obj F where
  app V := ModuleCat.ofHom (adjointApp f O ψ V)
  naturality {V V'} g := by
    ext s
    change restrictApp f O ψ _ (germ f O G V' (G.map g s))
      = F.restrictₛₗ ((Opens.map f).op.map g) (restrictApp f O ψ _ (germ f O G V s))
    rw [germ_naturality, restrictApp_naturality]

theorem abHom'_adjointHom {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)}
    (ψ : pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F) :
    abHom' f O (adjointHom f O ψ)
      = (TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
          (underlyingAb (ringsY f O) G) F.presheaf (abHom f O ψ) := by
  ext V s
  rw [adjAb_homEquiv_app]
  rfl

/-- **Stacks 008U for `f_*O`.** The module form of the adjunction `f_p ⊣ f_*`:
`Mor_{PMod(f_p f_*O)}(f_p G, F_{f_p f_*O}) ≃ Mor_{PMod(f_*O)}(G, f_*F)`,
`ψ ↦ (s ↦ ψ(germ of s))`. On underlying presheaves of abelian groups it is the adjunction
`f_p ⊣ f_*` of `TopCat.Presheaf`; that it respects the module structures is checked on germs,
using that `c_O` undoes the unit `f_*O ⟶ f_*f_pf_*O`. -/
noncomputable def pullbackHomEquiv (G : PresheafOfModules.{u} (ringsY f O))
    (F : PresheafOfModules.{u} (ringsX O)) :
    (pullbackObj f O G ⟶ (PresheafOfModules.restrictScalars (counitRings f O)).obj F) ≃
      (G ⟶ (pushforwardModules008V f (ringsX O)).obj F) where
  toFun ψ := adjointHom f O ψ
  invFun φ := PresheafOfModules.homMk
    (((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
      (underlyingAb (ringsY f O) G) F.presheaf).symm (abHom' f O φ))
    (fun U r x => symmApp_smul f O φ U r x)
  left_inv ψ := by
    apply (PresheafOfModules.toPresheaf _).map_injective
    change ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
      (underlyingAb (ringsY f O) G) F.presheaf).symm (abHom' f O (adjointHom f O ψ)) = abHom f O ψ
    rw [abHom'_adjointHom, Equiv.symm_apply_apply]
  right_inv φ := by
    refine PresheafOfModules.hom_ext fun V => ?_
    ext s
    change symmApp f O φ _ (germ f O G V s) = pushApp f O φ V s
    exact symmApp_germ_self f O φ V s

/-- The composite bijection `Mor(O ⊗_{p, f_p f_*O} f_p G, F) ≃ Mor(G, f_*F)` of Stacks 008V. -/
noncomputable def tensorPullbackHomEquiv (G : PresheafOfModules.{u} (ringsY f O))
    (F : PresheafOfModules.{u} (ringsX O)) :
    (tensorObj f O G ⟶ F) ≃ (G ⟶ (pushforwardModules008V f (ringsX O)).obj F) :=
  (tensorHomEquiv f O G F).trans (pullbackHomEquiv f O G F)

/-- On sections, `Ψ` corresponds to `s ↦ Ψ(1 ⊗ (germ of s))`. -/
theorem tensorPullbackHomEquiv_apply_app {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (Ψ : tensorObj f O G ⟶ F) (V : (Opens Y)ᵒᵖ)
    (s : G.obj V) :
    (tensorPullbackHomEquiv f O G F Ψ).app V s
      = tensorHomApp f O Ψ ((Opens.map f).op.obj V)
          ((1 : (ringsX O).obj _) ⊗ₜ pullbackAbUnit f (underlyingAb (ringsY f O) G) V s) :=
  rfl

theorem tensorPullbackHomEquiv_symm_apply_tmul {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (φ : G ⟶ (pushforwardModules008V f (ringsX O)).obj F)
    (U : (Opens X)ᵒᵖ) (b : (ringsX O).obj U) (x : (pullbackObj f O G).obj U) :
    tensorHomApp f O ((tensorPullbackHomEquiv f O G F).symm φ) U (b ⊗ₜ x)
      = b • restrictApp f O ((pullbackHomEquiv f O G F).symm φ) U x := rfl

theorem restrictApp_pullbackHomEquiv_symm {G : PresheafOfModules.{u} (ringsY f O)}
    {F : PresheafOfModules.{u} (ringsX O)} (φ : G ⟶ (pushforwardModules008V f (ringsX O)).obj F)
    (U : (Opens X)ᵒᵖ) (x : (pullbackObj f O G).obj U) :
    restrictApp f O ((pullbackHomEquiv f O G F).symm φ) U x
      = (((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
          (underlyingAb (ringsY f O) G) F.presheaf).symm (abHom' f O φ)).app U x := rfl

/-- **Stacks 008V.** Let `f : X ⟶ Y` be a continuous map of topological spaces and `O` a
presheaf of rings on `X`. The functor `G ↦ O ⊗_{p, f_p f_*O} f_p G` (`tensorPullback`), the
presheaf pullback `f_p G` of a presheaf of `f_*O`-modules tensored up to `O` sectionwise along
`c_O : f_p f_*O ⟶ O`, is left adjoint to the pushforward `f_* : PMod(O) ⥤ PMod(f_*O)`: for a
presheaf of `O`-modules `F` and a presheaf of `f_*O`-modules `G` the hom-set bijection
`Mor_{PMod(O)}(O ⊗_{p, f_p f_*O} f_p G, F) ≃ Mor_{PMod(f_*O)}(G, f_*F)`
(`tensorPullbackHomEquiv`) is natural in `G` and `F`. -/
@[stacks 008V "the explicit `O ⊗_{p, f_p f_*O} f_p (-)` is left adjoint to `f_*`"]
noncomputable def tensorPullbackAdjunction :
    tensorPullback f O ⊣ pushforwardModules008V f (ringsX O) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G F => tensorPullbackHomEquiv f O G F
      homEquiv_naturality_left_symm := fun {G' G F} h φ => by
        refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
        change tensorHomApp f O ((tensorPullbackHomEquiv f O G' F).symm (h ≫ φ)) U t
          = tensorHomApp f O ((tensorPullbackHomEquiv f O G F).symm φ) U (tensorMapApp f O h U t)
        induction t using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero, map_zero]
        | tmul b x =>
          rw [tensorMapApp_tmul, tensorPullbackHomEquiv_symm_apply_tmul,
            tensorPullbackHomEquiv_symm_apply_tmul, restrictApp_pullbackHomEquiv_symm,
            restrictApp_pullbackHomEquiv_symm, abHom'_comp,
            Adjunction.homEquiv_naturality_left_symm]
          rfl
        | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']
      homEquiv_naturality_right := fun {G F F'} Ψ k => by
        refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
        change (tensorPullbackHomEquiv f O G F' (Ψ ≫ k)).app V s
          = k.app _ ((tensorPullbackHomEquiv f O G F Ψ).app V s)
        rfl }


end Setting

end Stacks.PresheafOfModules.TensorPullback
