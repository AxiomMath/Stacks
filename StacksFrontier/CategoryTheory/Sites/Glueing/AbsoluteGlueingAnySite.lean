module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Over
import StacksCore.Tactic.StacksAttribute

/-!
# Glueing sheaves on an arbitrary site from absolute glueing data

Let `(C, J)` be a site, with `C` an arbitrary category — neither small nor essentially small — and
let `w` be an arbitrary universe.  An *absolute glueing datum for sheaves of `w`-sets on `C`*
consists of a sheaf `F_U` on each slice site `C/U`, together with an isomorphism
`c_f : j_f^{-1}F_U ≅ F_V` for each morphism `f : V ⟶ U` of `C`, subject to the cocycle condition
`c_g ∘ j_g^{-1}c_f = c_{f ∘ g}`.  Every sheaf `F` on `C` has its *canonical absolute glueing datum*
`(F|_{C/U}, c_f)`, and the assignment is an equivalence of categories.

This is the content of Stacks 0GWK, whose hypothesis is that `C` is a site: no smallness is
asked of it, and no universe is imposed on the sheaves.  The generality is load-bearing -- the
small étale site of an algebraic space over a scheme of universe `u` is a
`CategoryTheory.Category.{u, u + 1}` whose sheaves of sets are valued in `Type (u + 1)`, so it is
neither small nor are its sheaves valued in the universe of its objects.

## Main definitions

* `CategoryTheory.SiteGlueing.GlueingData`: absolute glueing data on an arbitrary site, and their
  category.
* `CategoryTheory.SiteGlueing.GlueingData.gluedSheaf`: the sheaf glued from a datum.
* `CategoryTheory.SiteGlueing.canonicalFunctor`: the canonical-glueing-data functor.
* `CategoryTheory.SiteGlueing.overMapComp`: the composition comparison for the restriction
  functors on sheaves of *modules*, which Mathlib has only for sheaves of sets.
* `CategoryTheory.SiteGlueing.ModuleGlueingData`: absolute glueing data for sheaves of modules
  over a sheaf of rings on an arbitrary site, and their category.
* `CategoryTheory.SiteGlueing.ModuleGlueingData.gluedSheaf`: the sheaf of modules glued from a
  datum.
* `CategoryTheory.SiteGlueing.canonicalModuleFunctor`: the canonical-glueing-data functor for
  sheaves of modules.

## Main results

* `CategoryTheory.SiteGlueing.isSheafFor_of_isSheaf_over`: a presheaf of sets is a sheaf for a
  covering sieve of an object as soon as its restriction to *one* slice site containing that
  object is a sheaf.
* `CategoryTheory.SiteGlueing.isSheaf_of_isSheaf_over`: a presheaf of sets is a sheaf as soon as
  its restriction to every slice site is.
* `CategoryTheory.SiteGlueing.canonicalEquivalence`: the category of sheaves of `w`-sets on `C` is
  equivalent to the category of absolute glueing data.
* `CategoryTheory.SiteGlueing.isSheaf_of_isSheaf_over'`: the same descent criterion for a
  presheaf with values in an arbitrary category.
* `CategoryTheory.SiteGlueing.canonicalModuleEquivalence`: **the module-coefficient form of the
  same statement** — for a sheaf of rings `R` on `C`, the category of sheaves of `R`-modules is
  equivalent to the category of absolute glueing data for sheaves of modules.

## Implementation notes

The quasi-inverse is the one the source gives: `F(U) := F_U(U/U)`, with restriction along
`f : V ⟶ U` obtained by restricting inside `F_U` along `j_f(V/V) ⟶ U/U` and then applying `c_f`
(`CategoryTheory.SiteGlueing.GlueingData.rho`).  Functoriality of this presheaf is the cocycle
condition (`CategoryTheory.SiteGlueing.GlueingData.rho_comp`); the normalisation `c_{𝟙} = id` that
the source does not state explicitly is *derived* from the cocycle condition, by observing that
`rho (𝟙 U)` is a split monomorphism and idempotent
(`CategoryTheory.SiteGlueing.GlueingData.rho_id`).

That the glued presheaf is a sheaf is proved in two steps.  First, its restriction to `C/V` is
isomorphic to `F_V` for every `V` (`CategoryTheory.SiteGlueing.GlueingData.theta`) — this is again
the cocycle condition.  Second, a presheaf of sets whose restriction to every slice site `C/V` is
a sheaf is itself a sheaf (`CategoryTheory.SiteGlueing.isSheaf_of_isSheaf_over`): the sheaf
condition for a covering sieve `S` of `V` matches, arrow by arrow, the sheaf condition on `C/V` for
the transported sieve `(Sieve.overEquiv (V/V)).symm S` at the tautological object `V/V`.

The equivalence is then assembled from full faithfulness and essential surjectivity of the
canonical-glueing-data functor.  Full faithfulness holds because a morphism of canonical glueing
data is determined by, and can be built from, its components at the tautological objects
(`CategoryTheory.SiteGlueing.app_hom_app_eq`); essential surjectivity is the construction above.

## Implementation notes on the module-coefficient form

The module-coefficient development is *not* a transport of the set-valued one: the glued object
has to be built as a `PresheafOfModules`, and every restriction map carries
`ModuleCat.restrictScalars` bookkeeping along the restriction map of `R`.  Three things make it
work.

* The composition comparison `CategoryTheory.SiteGlueing.overMapComp` has to be built by hand
  from `SheafOfModules.pushforwardComp` and `SheafOfModules.pushforwardCongr₂`: Mathlib supplies
  `CategoryTheory.GrothendieckTopology.overMapPullbackComp` for sheaves of sets and nothing for
  sheaves of modules.
* Every statement about the components is read **on sections**.  A morphism of `ModuleCat` is
  applied to an element only when its source and target are presented over *syntactically the
  same* ring: the coercion to a function is found by instance search, which does not unfold
  `Sheaf.over` or `CategoryTheory.Over.map`, so e.g. `F_U(j_f b)` must be written as
  `((SheafOfModules.overMap R f).obj (D.sheaf U)).val.obj (op b)` and not as
  `(D.sheaf U).val.obj (op ((Over.map f).obj b))`.  Where the two sides genuinely live over
  different objects of `C` — as for
  `CategoryTheory.SiteGlueing.ModuleGlueingData.thetaInvApp` — the function is applied through
  `CategoryTheory.ConcreteCategory.hom`.
* The chains of rewrites that the set-valued proofs do with `rw` and `slice_rhs` are written
  here as `calc` chains of `ConcreteCategory.congr_arg`: `rw` has to check that its motive is
  type-correct at instance transparency, and that check does not terminate for these types.
  For the same reason the two reductions `(M|_{C/U}).val.map k = M.val.map k.left` and
  `(Over.mapComp g f).hom.app b |>.left = 𝟙` are separate lemmas
  (`CategoryTheory.SiteGlueing.overFunctor_val_map_apply` and
  `CategoryTheory.SiteGlueing.mapComp_hom_app_left`): performed together in one `rfl` they
  exhaust the heartbeat budget, and raising the heartbeat limit is not permitted here.

`CategoryTheory.SiteGlueing.canonicalModuleEquivalence` carries **no** Stacks tag: 0GWK is a
statement about `Sh(C)`, the sheaves of *sets* on a site, and that statement is
`CategoryTheory.SiteGlueing.canonicalEquivalence` below.  Tag 0GWL, the only neighbouring
variant, is a remark about sheaves of sets on subcategories `U_τ ⊂ C/U` and is explicitly left
unproved by the source.  The Stacks project states no module-coefficient glueing lemma on a
general site; the module-coefficient form is recorded here because it is the construction that
the chartwise descriptions of modules on an algebraic space (Tags 03LY, 03LZ, 03M3) reduce to.

## References

* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
* [Stacks Project, Tag 0GWL](https://stacks.math.columbia.edu/tag/0GWL)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v₁ u₁ u v₂ u₂

namespace CategoryTheory.SiteGlueing

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- **The sheaf condition at one object, from the sheaf condition on one slice site containing
it.**  Let `Y` be an object of `C/U` and let `S` be a covering sieve of its underlying object
`Y.left`.  If the restriction of `P` to the slice site `C/U` is a sheaf, then `P` is a sheaf for
`S`: the sheaf condition for `S` matches, arrow by arrow, the sheaf condition on `C/U` for the
transported sieve `(Sieve.overEquiv Y).symm S` at `Y`.

The slice site is not required to be the one at `Y.left` itself, which is what makes this
usable when only *some* slices are known to carry the sheaf condition. -/
theorem isSheafFor_of_isSheaf_over {U : C} (P : Cᵒᵖ ⥤ Type w)
    (h : Presieve.IsSheaf (J.over U) ((Over.forget U).op ⋙ P))
    (Y : Over U) {S : Sieve Y.left} (hS : S ∈ J Y.left) :
    Presieve.IsSheafFor P S.arrows := by
  intro x hx
  set x' : Presieve.FamilyOfElements ((Over.forget U).op ⋙ P)
      ((Sieve.overEquiv Y).symm S).arrows :=
    fun _ g hg => x g.left ((Sieve.overEquiv_symm_iff S g).mp hg)
  have hx' : x'.Compatible := fun _ _ _ g₁ g₂ _ _ _ _ hcomm =>
    hx g₁.left g₂.left _ _ (by simpa using (Over.forget U).congr_map hcomm)
  have amalg : ∀ t : P.obj (op Y.left), x.IsAmalgamation t ↔ x'.IsAmalgamation t :=
    fun t => ⟨fun ht _ g _ => ht g.left _, fun ht _ g hg =>
      ht (Over.homMk g rfl : Over.mk (g ≫ Y.hom) ⟶ Y) ((Sieve.overEquiv_symm_iff S _).mpr hg)⟩
  obtain ⟨t, ht, huniq⟩ := h _ (J.overEquiv_symm_mem_over Y S hS) x' hx'
  exact ⟨t, (amalg t).mpr ht, fun t' ht' => huniq t' ((amalg t').mp ht')⟩

/-- If the restriction of a presheaf of sets to every slice site `C/V` is a sheaf, then the
presheaf is a sheaf.  This is
`CategoryTheory.SiteGlueing.isSheafFor_of_isSheaf_over` at the tautological object `V/V`. -/
theorem isSheaf_of_isSheaf_over (P : Cᵒᵖ ⥤ Type w)
    (h : ∀ V : C, Presieve.IsSheaf (J.over V) ((Over.forget V).op ⋙ P)) :
    Presieve.IsSheaf J P :=
  fun V _ hS => isSheafFor_of_isSheaf_over J P (h V) (Over.mk (𝟙 V)) hS

/-- If the restriction of a presheaf with values in an arbitrary category to every slice site
`C/V` is a sheaf, then the presheaf is a sheaf.  This is
`CategoryTheory.SiteGlueing.isSheaf_of_isSheaf_over` read through the definition of a sheaf with
values in a category: being a sheaf is being a sheaf of sets after applying every `coyoneda`. -/
theorem isSheaf_of_isSheaf_over' {A : Type u₂} [Category.{v₂} A] (P : Cᵒᵖ ⥤ A)
    (h : ∀ V : C, Presheaf.IsSheaf (J.over V) ((Over.forget V).op ⋙ P)) :
    Presheaf.IsSheaf J P :=
  fun E ↦ isSheaf_of_isSheaf_over J _ fun V ↦ h V E

/-- The tautological object `U/U` of the slice category `C/U`. -/
abbrev top (U : C) : Over U := Over.mk (𝟙 U)

/-- For `f : V ⟶ U`, the canonical morphism `j_f(V/V) ⟶ U/U` of `C/U`. -/
def topHom {V U : C} (f : V ⟶ U) : (Over.map f).obj (top V) ⟶ top U :=
  Over.homMk f (by simp)

/-- On underlying objects, the morphism `j_f(V/V) ⟶ U/U` is `f` itself. -/
@[simp] lemma topHom_left {V U : C} (f : V ⟶ U) : (topHom f).left = f := rfl

/-- `topHom (𝟙 U)` is an isomorphism: its source and target are both `U/U`, and it is the
identity of `U` on underlying objects. -/
instance isIso_topHom_id (U : C) : IsIso (topHom (𝟙 U)) :=
  ⟨Over.homMk (𝟙 U) (by simp), by ext; simp [topHom], by ext; simp [topHom]⟩

/-- For `b` in `C/V`, the canonical isomorphism `j_{b.hom}(b.left/b.left) ⟶ b` of `C/V`. -/
def sliceHom {V : C} (b : Over V) : (Over.map b.hom).obj (top b.left) ⟶ b :=
  Over.homMk (𝟙 b.left) (by simp)

/-- On underlying objects, `sliceHom b` is the identity of `b.left`. -/
@[simp] lemma sliceHom_left {V : C} (b : Over V) : (sliceHom b).left = 𝟙 b.left := rfl

/-- `sliceHom b` is an isomorphism, being the identity of `b.left` on underlying objects. -/
instance isIso_sliceHom {V : C} (b : Over V) : IsIso (sliceHom b) :=
  ⟨Over.homMk (𝟙 b.left) (by simp), by ext; simp [sliceHom], by ext; simp [sliceHom]⟩

/-- The inverse of `CategoryTheory.SiteGlueing.sliceHom b`, written out: it is again the
identity of `b.left` on underlying objects. -/
def sliceHomInv {V : C} (b : Over V) : b ⟶ (Over.map b.hom).obj (top b.left) :=
  Over.homMk (𝟙 b.left) (by simp)

/-- On underlying objects, `sliceHomInv b` is the identity of `b.left`. -/
@[simp] lemma sliceHomInv_left {V : C} (b : Over V) : (sliceHomInv b).left = 𝟙 b.left := rfl

/-- `sliceHomInv b` is a right inverse of `sliceHom b`. -/
@[simp] lemma sliceHomInv_sliceHom {V : C} (b : Over V) :
    sliceHomInv b ≫ sliceHom b = 𝟙 b := by
  ext
  simp [sliceHomInv, sliceHom]

/-- `sliceHomInv b` is a left inverse of `sliceHom b`. -/
@[simp] lemma sliceHom_sliceHomInv {V : C} (b : Over V) :
    sliceHom b ≫ sliceHomInv b = 𝟙 _ := by
  ext
  simp [sliceHomInv, sliceHom]

/-- **Absolute glueing data for sheaves of sets on a site** (Stacks, Sites, Section
"Glueing sheaves"): a sheaf `F_U` on each slice site `C/U`, an isomorphism
`c_f : j_f^{-1}F_U ≅ F_V` for each morphism `f : V ⟶ U` of `C`, such that
`c_g ∘ j_g^{-1}c_f = c_{f ∘ g}` for any two morphisms `f : V ⟶ U` and `g : W ⟶ V`. -/
structure GlueingData (J : GrothendieckTopology C) where
  /-- the sheaf on the slice site `C/U` -/
  sheaf (U : C) : Sheaf (J.over U) (Type w)
  /-- the comparison isomorphism `j_f^{-1}F_U ≅ F_V` for `f : V ⟶ U` -/
  iso {V U : C} (f : V ⟶ U) : (J.overMapPullback (Type w) f).obj (sheaf U) ≅ sheaf V
  /-- the cocycle condition `c_g ∘ j_g^{-1}c_f = c_{f ∘ g}` -/
  comp {W V U : C} (f : V ⟶ U) (g : W ⟶ V) :
    (J.overMapPullback (Type w) g).map (iso f).hom ≫ (iso g).hom
      = ((J.overMapPullbackComp (Type w) g f).app (sheaf U)).hom ≫ (iso (g ≫ f)).hom

namespace GlueingData

variable {J} (D : GlueingData.{w} J)

/-! ### The components of the comparison isomorphisms

The composites below are all between values of the sheaves `F_U` at objects of the slice
categories, spelled out.  Writing them this way (rather than through
`(J.overMapPullback _ f).obj (D.sheaf U)`) is what lets `rw` and `simp` see the types. -/

/-- The component of `c_f` at `b` in `C/V`, as an isomorphism `F_U(j_f b) ≅ F_V(b)`. -/
def isoAppIso {V U : C} (f : V ⟶ U) (b : Over V) :
    (D.sheaf U).obj.obj (op ((Over.map f).obj b)) ≅ (D.sheaf V).obj.obj (op b) :=
  (sheafToPresheaf (J.over V) (Type w) ⋙
    (evaluation (Over V)ᵒᵖ (Type w)).obj (op b)).mapIso (D.iso f)

/-- The component of `c_f` at `b` in `C/V`, as a map `F_U(j_f b) ⟶ F_V(b)`. -/
def isoApp {V U : C} (f : V ⟶ U) (b : Over V) :
    (D.sheaf U).obj.obj (op ((Over.map f).obj b)) ⟶ (D.sheaf V).obj.obj (op b) :=
  (D.isoAppIso f b).hom

/-- The component of `c_f⁻¹` at `b` in `C/V`, as a map `F_V(b) ⟶ F_U(j_f b)`. -/
def isoAppInv {V U : C} (f : V ⟶ U) (b : Over V) :
    (D.sheaf V).obj.obj (op b) ⟶ (D.sheaf U).obj.obj (op ((Over.map f).obj b)) :=
  (D.isoAppIso f b).inv

/-- The component of `c_f` at `b` followed by the component of `c_f⁻¹` is the identity of
`F_U(j_f b)`. -/
@[simp] lemma isoApp_isoAppInv {V U : C} (f : V ⟶ U) (b : Over V) :
    D.isoApp f b ≫ D.isoAppInv f b = 𝟙 _ := (D.isoAppIso f b).hom_inv_id

/-- The component of `c_f⁻¹` at `b` followed by the component of `c_f` is the identity of
`F_V(b)`. -/
@[simp] lemma isoAppInv_isoApp {V U : C} (f : V ⟶ U) (b : Over V) :
    D.isoAppInv f b ≫ D.isoApp f b = 𝟙 _ := (D.isoAppIso f b).inv_hom_id

/-- The components of `c_f` are natural in `b`: restricting inside `F_U` along `j_f h` and then
applying `c_f` is applying `c_f` and then restricting inside `F_V` along `h`. -/
lemma isoApp_naturality {V U : C} (f : V ⟶ U) {b b' : Over V} (h : b' ⟶ b) :
    (D.sheaf U).obj.map ((Over.map f).map h).op ≫ D.isoApp f b'
      = D.isoApp f b ≫ (D.sheaf V).obj.map h.op :=
  (D.iso f).hom.hom.naturality h.op

/-- The cocycle condition, read on components. -/
lemma isoApp_comp {W V U : C} (f : V ⟶ U) (g : W ⟶ V) (b : Over W) :
    D.isoApp f ((Over.map g).obj b) ≫ D.isoApp g b
      = (D.sheaf U).obj.map ((Over.mapComp g f).hom.app b).op ≫ D.isoApp (g ≫ f) b := by
  have h := NatTrans.congr_app
    (congrArg (fun (m : (J.overMapPullback (Type w) g).obj
        ((J.overMapPullback (Type w) f).obj (D.sheaf U)) ⟶ D.sheaf W) => m.hom) (D.comp f g))
    (op b)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Iso.app_hom,
    Functor.sheafPushforwardContinuous_map_hom_app,
    GrothendieckTopology.overMapPullbackComp_hom_app_hom_app] at h
  exact h

/-- The cocycle condition and the naturality of `c_f`, combined: restricting inside `F_U` along
the composite `j_{g ≫ f} b ⟶ j_f j_g b ⟶ j_f c` and applying `c_{g ≫ f}` is applying `c_f` at `c`,
restricting along `p : j_g b ⟶ c` inside `F_V`, and applying `c_g`. -/
private lemma map_isoApp_comp {W V U : C} (f : V ⟶ U) (g : W ⟶ V) {b : Over W} {c : Over V}
    (p : (Over.map g).obj b ⟶ c) :
    (D.sheaf U).obj.map ((Over.mapComp g f).hom.app b ≫ (Over.map f).map p).op
        ≫ D.isoApp (g ≫ f) b
      = D.isoApp f c ≫ (D.sheaf V).obj.map p.op ≫ D.isoApp g b := by
  rw [op_comp, Functor.map_comp, Category.assoc, ← D.isoApp_comp, ← Category.assoc,
    D.isoApp_naturality, Category.assoc]

/-- Equal morphisms have the same components of `c_f`, up to the `eqToHom` identifying `j_f b`
with `j_{f'} b`. -/
lemma isoApp_congr {V U : C} {f f' : V ⟶ U} (e : f = f') (b : Over V) :
    D.isoApp f b
      = (D.sheaf U).obj.map (eqToHom (congrArg (fun m => (Over.map m).obj b) e.symm)).op
        ≫ D.isoApp f' b := by
  subst e
  simp

/-! ### The glued presheaf -/

/-- The restriction map `F_U(U/U) ⟶ F_V(V/V)` attached to `f : V ⟶ U`: restrict along
`j_f(V/V) ⟶ U/U` inside `F_U`, then apply `c_f`. -/
def rho {V U : C} (f : V ⟶ U) :
    (D.sheaf U).obj.obj (op (top U)) ⟶ (D.sheaf V).obj.obj (op (top V)) :=
  (D.sheaf U).obj.map (topHom f).op ≫ D.isoApp f (top V)

/-- The canonical morphisms to the tautological objects factor through one another: after the
comparison `j_{g ≫ f} ≅ j_f j_g`, the morphism `topHom (g ≫ f)` is `j_f(topHom g)` followed by
`topHom f`. -/
lemma topHom_factor {W V U : C} (f : V ⟶ U) (g : W ⟶ V) :
    (Over.mapComp g f).hom.app (top W) ≫ (Over.map f).map (topHom g) ≫ topHom f
      = topHom (g ≫ f) := by
  ext
  simp [topHom, Over.mapComp]

/-- The restriction maps of the glued presheaf compose: `ρ_f ≫ ρ_g = ρ_{g ≫ f}`.  This is the
cocycle condition read on the tautological objects. -/
lemma rho_comp {W V U : C} (f : V ⟶ U) (g : W ⟶ V) :
    D.rho f ≫ D.rho g = D.rho (g ≫ f) := by
  rw [rho, rho, rho, Category.assoc, ← D.map_isoApp_comp f g (topHom g), ← Category.assoc,
    ← Functor.map_comp, ← op_comp, Category.assoc, topHom_factor]
/-- A retraction of `rho (𝟙 U)`, exhibiting it as a split monomorphism. -/
noncomputable def rhoIdRetraction (U : C) :
    (D.sheaf U).obj.obj (op (top U)) ⟶ (D.sheaf U).obj.obj (op (top U)) :=
  D.isoAppInv (𝟙 U) (top U) ≫ (D.sheaf U).obj.map (inv (topHom (𝟙 U))).op

/-- `rhoIdRetraction U` is a retraction of `ρ_{𝟙 U}`. -/
lemma rho_id_comp_retraction (U : C) : D.rho (𝟙 U) ≫ D.rhoIdRetraction U = 𝟙 _ := by
  rw [rho, rhoIdRetraction, Category.assoc, ← Category.assoc (D.isoApp (𝟙 U) (top U)),
    D.isoApp_isoAppInv, Category.id_comp, ← Functor.map_comp, ← op_comp, IsIso.inv_hom_id,
    op_id, Functor.map_id]

/-- `ρ_{𝟙 U}` is a monomorphism, being a split monomorphism. -/
instance mono_rho_id (U : C) : Mono (D.rho (𝟙 U)) :=
  mono_of_mono_fac (D.rho_id_comp_retraction U)

/-- `ρ_{𝟙 U}` is the identity.  This is the normalisation `c_{𝟙} = id`, which the cocycle
condition forces: `ρ_{𝟙 U}` is idempotent and a monomorphism. -/
@[simp] lemma rho_id (U : C) : D.rho (𝟙 U) = 𝟙 _ := by
  have h := D.rho_comp (𝟙 U) (𝟙 U)
  rw [congrArg (fun (m : U ⟶ U) => D.rho m) (Category.comp_id (𝟙 U))] at h
  exact (cancel_mono (D.rho (𝟙 U))).mp (h.trans (Category.id_comp _).symm)

/-! ### The glued presheaf restricted to a slice -/

/-- **The glued presheaf of an absolute glueing datum**: `U ↦ F_U(U/U)`. -/
@[simps]
def gluedPresheaf : Cᵒᵖ ⥤ Type w where
  obj U := (D.sheaf U.unop).obj.obj (op (top U.unop))
  map h := D.rho h.unop
  map_id U := D.rho_id U.unop
  map_comp h h' := (D.rho_comp h.unop h'.unop).symm

/-- The comparison map `F_V(b) ⟶ (glued presheaf)(b.left)`. -/
def thetaInvApp {V : C} (b : Over V) :
    (D.sheaf V).obj.obj (op b) ⟶ (D.sheaf b.left).obj.obj (op (top b.left)) :=
  (D.sheaf V).obj.map (sliceHom b).op ≫ D.isoApp b.hom (top b.left)

/-- The comparison maps `F_V(b) ⟶ (glued presheaf)(b.left)` are natural in `b`. -/
lemma thetaInvApp_naturality {V : C} {b b' : Over V} (k : b' ⟶ b) :
    (D.sheaf V).obj.map k.op ≫ D.thetaInvApp b' = D.thetaInvApp b ≫ D.rho k.left := by
  rw [thetaInvApp, thetaInvApp, rho, Category.assoc,
    ← D.map_isoApp_comp b.hom k.left (topHom k.left), D.isoApp_congr (Over.w k) (top b'.left)]
  simp only [← Functor.map_comp_assoc, ← op_comp]
  congr 3
  ext
  simp [sliceHom, topHom, Over.mapComp]

/-- The restriction of the glued presheaf to the slice site `C/V` is `F_V`. -/
@[simps]
def thetaInv (V : C) : (D.sheaf V).obj ⟶ (Over.forget V).op ⋙ D.gluedPresheaf where
  app b := D.thetaInvApp b.unop
  naturality _ _ k := D.thetaInvApp_naturality k.unop

/-- Each comparison map `F_V(b) ⟶ (glued presheaf)(b.left)` is an isomorphism, being the
composite of an isomorphism of `F_V` with a component of `c_{b.hom}`. -/
instance isIso_thetaInvApp {V : C} (b : Over V) : IsIso (D.thetaInvApp b) := by
  have h1 : IsIso ((D.sheaf V).obj.map (sliceHom b).op) := inferInstance
  have h2 : IsIso (D.isoApp b.hom (top b.left)) :=
    inferInstanceAs (IsIso (D.isoAppIso b.hom (top b.left)).hom)
  rw [thetaInvApp]
  exact IsIso.comp_isIso

/-- The comparison map `F_V ⟶ (glued presheaf)|_{C/V}` is an isomorphism, because every one of
its components is. -/
instance isIso_thetaInv (V : C) : IsIso (D.thetaInv V) := by
  have : ∀ b : (Over V)ᵒᵖ, IsIso ((D.thetaInv V).app b) :=
    fun b => D.isIso_thetaInvApp b.unop
  exact NatIso.isIso_of_isIso_app _

/-- The restriction of the glued presheaf to `C/V`, identified with `F_V`. -/
noncomputable def theta (V : C) : (Over.forget V).op ⋙ D.gluedPresheaf ≅ (D.sheaf V).obj :=
  (asIso (D.thetaInv V)).symm

/-- **The glued presheaf of an absolute glueing datum is a sheaf.** -/
theorem isSheaf_gluedPresheaf : Presieve.IsSheaf J D.gluedPresheaf :=
  isSheaf_of_isSheaf_over J _ fun V =>
    Presieve.isSheaf_iso (J.over V) (D.theta V).symm
      ((isSheaf_iff_isSheaf_of_type _ _).mp (D.sheaf V).property)

/-- The comparison maps are compatible with restriction along `Over.map f`. -/
lemma thetaInvApp_map {V U : C} (f : V ⟶ U) (b : Over V) :
    D.thetaInvApp ((Over.map f).obj b) = D.isoApp f b ≫ D.thetaInvApp b := by
  rw [thetaInvApp, thetaInvApp, ← D.map_isoApp_comp f b.hom (sliceHom b)]
  congr 3
  ext
  simp [sliceHom, Over.mapComp]

/-- **The sheaf glued from an absolute glueing datum.** -/
def gluedSheaf : Sheaf J (Type w) :=
  ⟨D.gluedPresheaf, (isSheaf_iff_isSheaf_of_type _ _).mpr D.isSheaf_gluedPresheaf⟩

/-! ### The category of absolute glueing data -/

/-- A morphism of absolute glueing data: a compatible family of morphisms `F_U ⟶ G_U`. -/
@[ext]
structure Hom (D E : GlueingData.{w} J) where
  /-- the morphism `F_U ⟶ G_U` on the slice site `C/U` -/
  app (U : C) : D.sheaf U ⟶ E.sheaf U
  /-- compatibility with the comparison isomorphisms -/
  w {V U : C} (f : V ⟶ U) :
    (J.overMapPullback (Type w) f).map (app U) ≫ (E.iso f).hom = (D.iso f).hom ≫ app V

attribute [reassoc] Hom.w

/-- Absolute glueing data form a category, a morphism being a family of morphisms `F_U ⟶ G_U`
compatible with the comparison isomorphisms. -/
instance : Category (GlueingData.{w} J) where
  Hom := Hom
  id D := { app := fun _ => 𝟙 _, w := fun _ => by simp }
  comp α β :=
    { app := fun U => α.app U ≫ β.app U
      w := fun f => by
        rw [Functor.map_comp, Category.assoc, Hom.w, ← Category.assoc, Hom.w, Category.assoc] }

/-- The identity morphism of an absolute glueing datum is the identity on each slice site. -/
@[simp] lemma id_app (D : GlueingData.{w} J) (U : C) :
    Hom.app (𝟙 D) U = 𝟙 (D.sheaf U) := rfl

/-- Morphisms of absolute glueing data compose slice site by slice site. -/
@[simp] lemma comp_app {D E F : GlueingData.{w} J} (α : D ⟶ E) (β : E ⟶ F) (U : C) :
    Hom.app (α ≫ β) U = α.app U ≫ β.app U := rfl

/-- Two morphisms of absolute glueing data that agree on every slice site are equal. -/
@[ext] lemma hom_ext {D E : GlueingData.{w} J} {α β : D ⟶ E}
    (h : ∀ U, α.app U = β.app U) : α = β :=
  Hom.ext (funext h)

end GlueingData

/-- A morphism of absolute glueing data all of whose components are isomorphisms is an
isomorphism. -/
lemma GlueingData.isIso_of_isIso_app {D E : GlueingData.{w} J} (α : D ⟶ E)
    (h : ∀ U, IsIso (α.app U)) : IsIso α := by
  refine ⟨⟨{ app := fun U => inv (α.app U), w := fun {V U} f => ?_ }, ?_, ?_⟩⟩
  · have hα := α.w f
    rw [IsIso.eq_comp_inv, Category.assoc, ← hα, ← Category.assoc, ← Functor.map_comp,
      IsIso.inv_hom_id, Functor.map_id, Category.id_comp]
  · exact GlueingData.hom_ext fun U => IsIso.hom_inv_id (α.app U)
  · exact GlueingData.hom_ext fun U => IsIso.inv_hom_id (α.app U)

/-! ### The canonical absolute glueing datum of a sheaf -/

/-- The canonical absolute glueing datum of a sheaf `F` on `C`: the family of restrictions
`F|_{C/U}` together with the canonical isomorphisms `j_f^{-1}(F|_{C/U}) ≅ F|_{C/V}`. -/
@[simps]
def canonicalGlueingData (F : Sheaf J (Type w)) : GlueingData.{w} J where
  sheaf U := F.over U
  iso f := F.pushforwardOverMapIso f
  comp f g := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun b => ?_)
    ext t
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Iso.app_hom,
      Functor.sheafPushforwardContinuous_map_hom_app,
      GrothendieckTopology.overMapPullbackComp_hom_app_hom_app,
      Sheaf.pushforwardOverMapIso_hom_hom_app]
    simp only [Over.map_obj_left, TypeCat.Fun.toFun_apply, Over.mapComp, Functor.comp_obj,
      NatIso.ofComponents_hom_app, Functor.sheafPushforwardContinuous_obj_obj_map, Over.forget_obj,
      Quiver.Hom.unop_op, Over.forget_map, Over.isoMk_hom_left, Iso.refl_hom, op_id, Functor.map_id]
    rfl

/-- **The canonical-glueing-data functor** `Sh(C) ⥤ (absolute glueing data)`. -/
def canonicalFunctor : Sheaf J (Type w) ⥤ GlueingData.{w} J where
  obj F := canonicalGlueingData J F
  map {F G} ψ :=
    { app := fun U => (J.overPullback (Type w) U).map ψ
      w := fun f => by
        apply Sheaf.hom_ext
        refine NatTrans.ext (funext fun b => ?_)
        ext t
        simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
        rfl }
  map_id F := GlueingData.hom_ext fun U => (J.overPullback (Type w) U).map_id F
  map_comp ψ ψ' :=
    GlueingData.hom_ext fun U => (J.overPullback (Type w) U).map_comp ψ ψ'

/-! ### `canonicalFunctor` is fully faithful -/

section FullyFaithful

variable {F G : Sheaf J (Type w)} (α : canonicalGlueingData J F ⟶ canonicalGlueingData J G)

/-- A morphism of canonical glueing data is determined by the values of its components at the
tautological objects: the component of `α_U` at `b` in `C/U` agrees with the component of
`α_{b.left}` at `b.left/b.left`. -/
lemma app_hom_app_eq (U : C) (b : Over U) :
    (α.app U).hom.app (op b) = (α.app b.left).hom.app (op (top b.left)) := by
  have hw0 := NatTrans.congr_app (congrArg
    (fun (m : (J.overMapPullback (Type w) b.hom).obj (F.over U) ⟶ G.over b.left) => m.hom)
    (α.w b.hom)) (op (top b.left))
  simp only [canonicalGlueingData_iso, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, Functor.sheafPushforwardContinuous_map_hom_app,
    Sheaf.pushforwardOverMapIso_hom_hom_app] at hw0
  have hw : (α.app U).hom.app (op ((Over.map b.hom).obj (top b.left)))
      = (α.app b.left).hom.app (op (top b.left)) :=
    (Category.comp_id _).symm.trans (hw0.trans (Category.id_comp _))
  have hnat : (α.app U).hom.app (op ((Over.map b.hom).obj (top b.left)))
      = (α.app U).hom.app (op b) := by
    have h := (α.app U).hom.naturality (sliceHom b).op
    have hF : ((canonicalGlueingData J F).sheaf U).obj.map (sliceHom b).op
        = 𝟙 (F.obj.obj (op b.left)) := F.obj.map_id (op b.left)
    have hG : ((canonicalGlueingData J G).sheaf U).obj.map (sliceHom b).op
        = 𝟙 (G.obj.obj (op b.left)) := G.obj.map_id (op b.left)
    rw [hF, hG] at h
    exact (Category.id_comp _).symm.trans (h.trans (Category.comp_id _))
  exact hnat.symm.trans hw

/-- The map of sheaves on `C` underlying a morphism of canonical glueing data. -/
def ofGlueingHom : F ⟶ G :=
  Sheaf.homEquiv.symm
    { app := fun b => (α.app b.unop).hom.app (op (top b.unop))
      naturality := fun b b' h => by
        have hnat := (α.app b.unop).hom.naturality
          (Over.homMk h.unop (by simp) : Over.mk h.unop ⟶ top b.unop).op
        have hF : ((canonicalGlueingData J F).sheaf b.unop).obj.map
              (Over.homMk h.unop (by simp) : Over.mk h.unop ⟶ top b.unop).op
            = F.obj.map h := rfl
        have hG : ((canonicalGlueingData J G).sheaf b.unop).obj.map
              (Over.homMk h.unop (by simp) : Over.mk h.unop ⟶ top b.unop).op
            = G.obj.map h := rfl
        rw [hF, hG, app_hom_app_eq J α b.unop (Over.mk h.unop)] at hnat
        exact hnat }

/-- `ofGlueingHom` is a right inverse of `canonicalFunctor` on morphisms: the morphism of
canonical glueing data induced by `ofGlueingHom α` is `α`. -/
lemma canonicalFunctor_map_ofGlueingHom :
    (canonicalFunctor J).map (ofGlueingHom J α) = α :=
  GlueingData.hom_ext fun U => Sheaf.hom_ext
    (NatTrans.ext (funext fun b => (app_hom_app_eq J α U b.unop).symm))

end FullyFaithful

/-- `canonicalFunctor` is faithful: a morphism of sheaves is read off from the components of the
induced morphism of glueing data at the tautological objects. -/
instance : (canonicalFunctor.{w} J).Faithful where
  map_injective {F G} {_ψ _ψ'} h :=
    Sheaf.hom_ext (NatTrans.ext (funext fun b =>
      congrArg (fun (β : canonicalGlueingData J F ⟶ canonicalGlueingData J G) =>
        (β.app b.unop).hom.app (op (top b.unop))) h))

/-- `canonicalFunctor` is full, a preimage of `α` being `ofGlueingHom α`. -/
instance : (canonicalFunctor.{w} J).Full where
  map_surjective α := ⟨ofGlueingHom J α, canonicalFunctor_map_ofGlueingHom J α⟩

/-! ### `canonicalFunctor` is essentially surjective, hence an equivalence -/

section EssSurj

variable (D : GlueingData.{w} J)

/-- The comparison morphism `F_U ⟶ (glued sheaf)|_{C/U}` is an isomorphism of sheaves: it is one
of presheaves, and `sheafToPresheaf` is fully faithful. -/
instance isIso_thetaInvSheaf (U : C) :
    IsIso (Sheaf.homEquiv.symm (D.thetaInv U) : D.sheaf U ⟶ D.gluedSheaf.over U) := by
  have : IsIso ((sheafToPresheaf (J.over U) (Type w)).map
      (Sheaf.homEquiv.symm (D.thetaInv U) : D.sheaf U ⟶ D.gluedSheaf.over U)) :=
    D.isIso_thetaInv U
  exact isIso_of_fully_faithful (sheafToPresheaf (J.over U) (Type w)) _

/-- The comparison morphism from an absolute glueing datum to the canonical glueing datum of the
sheaf glued from it. -/
def toCanonicalGlueingData : D ⟶ canonicalGlueingData J D.gluedSheaf where
  app U := Sheaf.homEquiv.symm (D.thetaInv U)
  w {V U} f := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun b => ?_)
    have h : D.thetaInvApp ((Over.map f).obj b.unop)
        = D.isoApp f b.unop ≫ D.thetaInvApp b.unop := D.thetaInvApp_map f b.unop
    simp only [canonicalGlueingData_iso, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, Functor.sheafPushforwardContinuous_map_hom_app,
      Sheaf.pushforwardOverMapIso_hom_hom_app]
    exact (Category.comp_id _).trans h

/-- The comparison morphism from an absolute glueing datum to the canonical glueing datum of the
sheaf glued from it is an isomorphism. -/
instance : IsIso (toCanonicalGlueingData J D) :=
  GlueingData.isIso_of_isIso_app J _ fun U => isIso_thetaInvSheaf J D U

end EssSurj

/-- `canonicalFunctor` is essentially surjective: every absolute glueing datum is isomorphic to
the canonical glueing datum of the sheaf glued from it. -/
instance : (canonicalFunctor.{w} J).EssSurj where
  mem_essImage D := ⟨D.gluedSheaf, ⟨(asIso (toCanonicalGlueingData J D)).symm⟩⟩

/-- `canonicalFunctor` is an equivalence, being fully faithful and essentially surjective. -/
instance : (canonicalFunctor.{w} J).IsEquivalence where

/-- **Stacks 0GWK.** For a site `C`, with no smallness hypothesis and with sheaves of sets
valued in an arbitrary universe, the category of sheaves on `C` is equivalent to the category of
absolute glueing data, via the functor sending a sheaf to its canonical absolute glueing data. -/
@[stacks 0GWK]
noncomputable def canonicalEquivalence : Sheaf J (Type w) ≌ GlueingData.{w} J :=
  (canonicalFunctor J).asEquivalence

/-! ### Glueing sheaves of modules -/

section Modules

variable {J} (R : Sheaf J RingCat.{u})

/-- The comparison of iterated slice restriction with restriction along the composite is the
identity on underlying objects. -/
lemma mapComp_hom_app_left {W V U : C} (f : V ⟶ U) (g : W ⟶ V) (b : Over W) :
    ((Over.mapComp g f).hom.app b).left = 𝟙 b.left := rfl

/-- Restricting the restriction of a sheaf of modules to a slice site along a morphism of the
slice is restricting the sheaf itself along the underlying morphism. -/
lemma overFunctor_val_map_apply (M : SheafOfModules.{w} R) (U : C) {b b' : Over U} (k : b ⟶ b')
    (x : (M.over U).val.obj (op b')) :
    (M.over U).val.map k.op x = M.val.map k.left.op x := rfl

/-- A presheaf of modules restricts along an identity as the identity, read on sections. -/
lemma presheafOfModules_map_id_apply {S : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{w} S)
    (X : Cᵒᵖ) (x : M.obj X) : M.map (𝟙 X) x = x := by
  rw [M.map_id]; rfl

/-- **The composition comparison for the restriction functors of sheaves of modules.** For
morphisms `g : W ⟶ V` and `f : V ⟶ U` of `C`, restricting a sheaf of `R|_{C/U}`-modules along
`f` and then along `g` is restricting it along `g ≫ f`. This is `SheafOfModules.pushforwardComp`
read through `CategoryTheory.Over.mapComp`; Mathlib has the comparison for sheaves of sets
(`GrothendieckTopology.overMapPullbackComp`) but not for sheaves of modules. -/
noncomputable def overMapComp {W V U : C} (f : V ⟶ U) (g : W ⟶ V) :
    SheafOfModules.overMap.{w} R f ⋙ SheafOfModules.overMap.{w} R g ≅
      SheafOfModules.overMap.{w} R (g ≫ f) :=
  letI : (Over.map g ⋙ Over.map f).IsContinuous (J.over W) (J.over U) :=
    Functor.isContinuous_comp _ _ _ (J.over V) _
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (Over.mapComp g f)
      (by
        ext b : 3
        dsimp
        simp [Over.mapComp]
        rfl)

/-- The composition comparison of restrictions of sheaves of modules, read on sections: it is
the restriction map of `M` along the comparison `CategoryTheory.Over.mapComp`. -/
lemma overMapComp_hom_app_val_app {W V U : C} (f : V ⟶ U) (g : W ⟶ V)
    (M : SheafOfModules.{w} (R.over U)) (b : Over W)
    (x : ((SheafOfModules.overMap R f ⋙ SheafOfModules.overMap R g).obj M).val.obj (op b)) :
    ((overMapComp R f g).hom.app M).val.app (op b) x =
      M.val.map ((Over.mapComp g f).hom.app b).op x := rfl

/-- **Absolute glueing data for sheaves of modules on a site**: a sheaf `F_U` of
`R|_{C/U}`-modules on each slice site `C/U`, an isomorphism `c_f : j_f^{-1}F_U ≅ F_V` for each
morphism `f : V ⟶ U` of `C`, such that `c_g ∘ j_g^{-1}c_f = c_{f ∘ g}` for any two morphisms
`f : V ⟶ U` and `g : W ⟶ V`. This is the module-coefficient analogue of
`CategoryTheory.SiteGlueing.GlueingData`. -/
structure ModuleGlueingData where
  /-- the sheaf of modules on the slice site `C/U` -/
  sheaf (U : C) : SheafOfModules.{w} (R.over U)
  /-- the comparison isomorphism `j_f^{-1}F_U ≅ F_V` for `f : V ⟶ U` -/
  iso {V U : C} (f : V ⟶ U) : (SheafOfModules.overMap R f).obj (sheaf U) ≅ sheaf V
  /-- the cocycle condition `c_g ∘ j_g^{-1}c_f = c_{f ∘ g}` -/
  comp {W V U : C} (f : V ⟶ U) (g : W ⟶ V) :
    (SheafOfModules.overMap R g).map (iso f).hom ≫ (iso g).hom =
      (overMapComp R f g).hom.app (sheaf U) ≫ (iso (g ≫ f)).hom

namespace ModuleGlueingData

variable {R} (D : ModuleGlueingData.{w} R)

/-- The component of `c_f` at `b` in `C/V`, as an isomorphism `F_U(j_f b) ≅ F_V(b)` of modules
over the sections of `R` on `b.left`. -/
noncomputable def isoAppIso {V U : C} (f : V ⟶ U) (b : Over V) :
    ((SheafOfModules.overMap R f).obj (D.sheaf U)).val.obj (op b) ≅
      (D.sheaf V).val.obj (op b) :=
  (SheafOfModules.evaluation (R.over V) (op b)).mapIso (D.iso f)

/-- The component of `c_f` at `b` in `C/V`, as a map `F_U(j_f b) ⟶ F_V(b)`. -/
noncomputable def isoApp {V U : C} (f : V ⟶ U) (b : Over V) :
    ((SheafOfModules.overMap R f).obj (D.sheaf U)).val.obj (op b) ⟶
      (D.sheaf V).val.obj (op b) :=
  (D.isoAppIso f b).hom

/-- The component of `c_f⁻¹` at `b` in `C/V`, as a map `F_V(b) ⟶ F_U(j_f b)`. -/
noncomputable def isoAppInv {V U : C} (f : V ⟶ U) (b : Over V) :
    (D.sheaf V).val.obj (op b) ⟶
      ((SheafOfModules.overMap R f).obj (D.sheaf U)).val.obj (op b) :=
  (D.isoAppIso f b).inv

/-- The component of `c_f` followed by the component of `c_f⁻¹` is the identity, on sections. -/
lemma isoAppInv_isoApp_apply {V U : C} (f : V ⟶ U) (b : Over V)
    (x : ((SheafOfModules.overMap R f).obj (D.sheaf U)).val.obj (op b)) :
    D.isoAppInv f b (D.isoApp f b x) = x := by
  simp [isoApp, isoAppInv]

/-- The component of `c_f⁻¹` followed by the component of `c_f` is the identity, on sections. -/
lemma isoApp_isoAppInv_apply {V U : C} (f : V ⟶ U) (b : Over V)
    (x : (D.sheaf V).val.obj (op b)) :
    D.isoApp f b (D.isoAppInv f b x) = x := by
  simp [isoApp, isoAppInv]

/-- The components of `c_f` are injective on sections, being components of an isomorphism. -/
lemma isoApp_injective {V U : C} (f : V ⟶ U) (b : Over V) :
    Function.Injective (D.isoApp f b) := fun y z h ↦ by
  rw [← D.isoAppInv_isoApp_apply f b y, h, D.isoAppInv_isoApp_apply]

/-- The components of `c_f` are natural in `b`: restricting inside `F_U` along `j_f h` and then
applying `c_f` is applying `c_f` and then restricting inside `F_V` along `h`. -/
lemma isoApp_naturality_apply {V U : C} (f : V ⟶ U) {b b' : Over V} (h : b' ⟶ b)
    (x : ((SheafOfModules.overMap R f).obj (D.sheaf U)).val.obj (op b)) :
    D.isoApp f b' ((D.sheaf U).val.map ((Over.map f).map h).op x) =
      (D.sheaf V).val.map h.op (D.isoApp f b x) :=
  PresheafOfModules.naturality_apply (D.iso f).hom.val h.op x

/-- The cocycle condition, read on sections. -/
lemma isoApp_comp_apply {W V U : C} (f : V ⟶ U) (g : W ⟶ V) (b : Over W)
    (x : ((SheafOfModules.overMap R f).obj (D.sheaf U)).val.obj (op ((Over.map g).obj b))) :
    D.isoApp g b (D.isoApp f ((Over.map g).obj b) x) =
      D.isoApp (g ≫ f) b ((D.sheaf U).val.map ((Over.mapComp g f).hom.app b).op x) :=
  ConcreteCategory.congr_hom
    (congrArg (fun (φ : (SheafOfModules.overMap R g).obj
        ((SheafOfModules.overMap R f).obj (D.sheaf U)) ⟶ D.sheaf W) ↦ φ.val.app (op b))
      (D.comp f g)) x

/-- The cocycle condition and the naturality of `c_f`, combined and read on sections: see
`CategoryTheory.SiteGlueing.GlueingData.map_isoApp_comp` for the statement. -/
private lemma isoApp_map_isoApp_apply {W V U : C} (f : V ⟶ U) (g : W ⟶ V) {b : Over W}
    {c : Over V} (p : (Over.map g).obj b ⟶ c)
    (x : ((SheafOfModules.overMap R f).obj (D.sheaf U)).val.obj (op c)) :
    D.isoApp g b ((D.sheaf V).val.map p.op (D.isoApp f c x)) =
      D.isoApp (g ≫ f) b ((D.sheaf U).val.map
        ((Over.mapComp g f).hom.app b ≫ (Over.map f).map p).op x) :=
  calc D.isoApp g b ((D.sheaf V).val.map p.op (D.isoApp f c x))
      = D.isoApp g b (D.isoApp f ((Over.map g).obj b)
          ((D.sheaf U).val.map ((Over.map f).map p).op x)) :=
        ConcreteCategory.congr_arg _ (D.isoApp_naturality_apply f p x).symm
    _ = D.isoApp (g ≫ f) b ((D.sheaf U).val.map ((Over.mapComp g f).hom.app b).op
          ((D.sheaf U).val.map ((Over.map f).map p).op x)) :=
        D.isoApp_comp_apply f g b _
    _ = _ := ConcreteCategory.congr_arg _ ((D.sheaf U).val.map_comp_apply
          ((Over.map f).map p).op ((Over.mapComp g f).hom.app b).op x).symm

/-- Equal morphisms have the same components of `c_f`, up to the restriction map identifying
`j_f b` with `j_{f'} b`. -/
lemma isoApp_congr_apply {V U : C} {f f' : V ⟶ U} (e : f = f') (b : Over V)
    (x : ((SheafOfModules.overMap R f).obj (D.sheaf U)).val.obj (op b)) :
    D.isoApp f b x =
      D.isoApp f' b ((D.sheaf U).val.map
        (eqToHom (congrArg (fun m ↦ (Over.map m).obj b) e.symm)).op x) := by
  subst e
  rw [eqToHom_refl, op_id, PresheafOfModules.map_id]
  rfl

/-- The restriction map `F_U(U/U) ⟶ F_V(V/V)` attached to `f : V ⟶ U`, semilinear over the
restriction map of `R`: restrict along `j_f(V/V) ⟶ U/U` inside `F_U`, then apply `c_f`. -/
noncomputable def rho {V U : C} (f : V ⟶ U) :
    (D.sheaf U).val.obj (op (top U)) ⟶
      (ModuleCat.restrictScalars ((R.over U).obj.map (topHom f).op).hom).obj
        ((D.sheaf V).val.obj (op (top V))) :=
  (D.sheaf U).val.map (topHom f).op ≫
    (ModuleCat.restrictScalars ((R.over U).obj.map (topHom f).op).hom).map
      (D.isoApp f (top V))

/-- The restriction maps of the glued presheaf of modules, read on sections. -/
lemma rho_apply {V U : C} (f : V ⟶ U) (x : (D.sheaf U).val.obj (op (top U))) :
    D.rho f x = D.isoApp f (top V) ((D.sheaf U).val.map (topHom f).op x) := rfl

/-- The restriction maps of the glued presheaf of modules compose: `ρ_f ≫ ρ_g = ρ_{g ≫ f}`.
This is the cocycle condition read on the tautological objects. -/
lemma rho_comp_apply {W V U : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : (D.sheaf U).val.obj (op (top U))) :
    D.rho g (D.rho f x) = D.rho (g ≫ f) x := by
  show D.isoApp g (top W) ((D.sheaf V).val.map (topHom g).op
        (D.isoApp f (top V) ((D.sheaf U).val.map (topHom f).op x))) =
      D.isoApp (g ≫ f) (top W) ((D.sheaf U).val.map (topHom (g ≫ f)).op x)
  refine (D.isoApp_map_isoApp_apply f g (topHom g) _).trans (ConcreteCategory.congr_arg _ ?_)
  exact ((D.sheaf U).val.map_comp_apply (topHom f).op
      ((Over.mapComp g f).hom.app (top W) ≫ (Over.map f).map (topHom g)).op x).symm.trans
    (congrArg (fun (m : (Over.map (g ≫ f)).obj (top W) ⟶ top U) ↦ (D.sheaf U).val.map m.op x)
      (by simpa using GlueingData.topHom_factor f g))

/-- `ρ_{𝟙 U}` is the identity.  This is the normalisation `c_{𝟙} = id`, which the cocycle
condition forces: `ρ_{𝟙 U}` is idempotent and injective on sections. -/
lemma rho_id_apply (U : C) (x : (D.sheaf U).val.obj (op (top U))) : D.rho (𝟙 U) x = x := by
  have hinj : Function.Injective (D.rho (𝟙 U)) := by
    intro y z h
    rw [rho_apply, rho_apply] at h
    have h' := D.isoApp_injective (𝟙 U) (top U) h
    have hid : ∀ t : (D.sheaf U).val.obj (op (top U)),
        (D.sheaf U).val.map (inv (topHom (𝟙 U))).op
            ((D.sheaf U).val.map (topHom (𝟙 U)).op t) = t := by
      intro t
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id,
        PresheafOfModules.map_id]
      rfl
    rw [← hid y, h', hid]
  refine hinj ?_
  rw [D.rho_comp_apply (𝟙 U) (𝟙 U), Category.comp_id]

/-- **The glued presheaf of modules of an absolute glueing datum**: `U ↦ F_U(U/U)`. -/
noncomputable def gluedPresheaf : PresheafOfModules.{w} R.obj where
  obj X := (D.sheaf X.unop).val.obj (op (top X.unop))
  map h := D.rho h.unop
  map_id X := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x ↦ ?_)
    exact D.rho_id_apply X.unop x
  map_comp h h' := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x ↦ ?_)
    exact (D.rho_comp_apply h.unop h'.unop x).symm

/-- The restriction maps of the glued presheaf of modules are the maps `ρ`. -/
lemma gluedPresheaf_map_apply {V U : C} (f : V ⟶ U)
    (x : (D.sheaf U).val.obj (op (top U))) :
    D.gluedPresheaf.map f.op x = D.rho f x := rfl

/-- The comparison map `F_V(b) ⟶ (glued presheaf)(b.left)`. -/
noncomputable def thetaInvApp {V : C} (b : Over V) :
    (D.sheaf V).val.obj (op b) ⟶ D.gluedPresheaf.obj (op b.left) :=
  (D.sheaf V).val.map (sliceHom b).op ≫
    (ModuleCat.restrictScalarsId'App ((R.over V).obj.map (sliceHom b).op).hom
      (by simp; rfl) _).hom ≫ D.isoApp b.hom (top b.left)

/-- The comparison map `F_V(b) ⟶ (glued presheaf)(b.left)`, read on sections. -/
lemma thetaInvApp_apply {V : C} (b : Over V) (x : (D.sheaf V).val.obj (op b)) :
    ConcreteCategory.hom (D.thetaInvApp b) x =
      D.isoApp b.hom (top b.left) ((D.sheaf V).val.map (sliceHom b).op x) := rfl

/-- The morphism of `C/V` through which the comparison maps are natural: the composite of the
comparison of iterated restriction with the canonical morphisms to the tautological objects is
the restriction along `k`. -/
lemma sliceHom_naturality {V : C} {b b' : Over V} (k : b' ⟶ b) :
    eqToHom (congrArg (fun m ↦ (Over.map m).obj (top b'.left)) (Over.w k).symm) ≫
        (Over.mapComp k.left b.hom).hom.app (top b'.left) ≫
          (Over.map b.hom).map (topHom k.left) ≫ sliceHom b =
      sliceHom b' ≫ k := by
  ext
  simp [sliceHom, topHom, Over.mapComp, Over.eqToHom_left]

/-- The comparison maps `thetaInvApp` are natural in `b`: on sections, restricting along `k`
and then comparing agrees with comparing and then applying the restriction map of the glued
presheaf along `k.left`. -/
lemma thetaInvApp_naturality_apply {V : C} {b b' : Over V} (k : b' ⟶ b)
    (x : (D.sheaf V).val.obj (op b)) :
    ConcreteCategory.hom (D.thetaInvApp b') ((D.sheaf V).val.map k.op x) =
      D.gluedPresheaf.map k.left.op (ConcreteCategory.hom (D.thetaInvApp b) x) := by
  show D.isoApp b'.hom (top b'.left) ((D.sheaf V).val.map (sliceHom b').op
        ((D.sheaf V).val.map k.op x)) =
      D.rho k.left (D.isoApp b.hom (top b.left) ((D.sheaf V).val.map (sliceHom b).op x))
  have hL : D.isoApp b'.hom (top b'.left) ((D.sheaf V).val.map (sliceHom b').op
        ((D.sheaf V).val.map k.op x)) =
      D.isoApp b'.hom (top b'.left) ((D.sheaf V).val.map (sliceHom b' ≫ k).op x) :=
    ConcreteCategory.congr_arg _
      ((D.sheaf V).val.map_comp_apply k.op (sliceHom b').op x).symm
  have hR : D.rho k.left (D.isoApp b.hom (top b.left)
        ((D.sheaf V).val.map (sliceHom b).op x)) =
      D.isoApp k.left (top b'.left) ((D.sheaf b.left).val.map (topHom k.left).op
        (D.isoApp b.hom (top b.left) ((D.sheaf V).val.map (sliceHom b).op x))) := rfl
  refine hL.trans (hR.trans ?_).symm
  refine (D.isoApp_map_isoApp_apply b.hom k.left (topHom k.left) _).trans
    ((D.isoApp_congr_apply (Over.w k) (top b'.left) _).trans (ConcreteCategory.congr_arg _ ?_))
  rw [← sliceHom_naturality k]
  simp only [op_comp, PresheafOfModules.map_comp_apply]
  exact ConcreteCategory.congr_arg _ ((D.sheaf V).val.map_comp_apply _ _ _)

/-- The comparison map `(glued presheaf)(b.left) ⟶ F_V(b)` inverse to
`CategoryTheory.SiteGlueing.ModuleGlueingData.thetaInvApp`. -/
noncomputable def thetaApp {V : C} (b : Over V) :
    D.gluedPresheaf.obj (op b.left) ⟶ (D.sheaf V).val.obj (op b) :=
  D.isoAppInv b.hom (top b.left) ≫ (D.sheaf V).val.map (sliceHomInv b).op ≫
    (ModuleCat.restrictScalarsId'App ((R.over V).obj.map (sliceHomInv b).op).hom
      (by simp; rfl) _).hom

/-- The inverse comparison map, read on sections. -/
lemma thetaApp_apply {V : C} (b : Over V) (x : D.gluedPresheaf.obj (op b.left)) :
    ConcreteCategory.hom (D.thetaApp b) x =
      (D.sheaf V).val.map (sliceHomInv b).op (D.isoAppInv b.hom (top b.left) x) := rfl

/-- Restricting inside `F_V` along a split morphism of `C/V` and then along its section is the
identity, on sections. -/
lemma map_eq_self {V : C} {b b' : Over V} (e : b' ⟶ b) (e' : b ⟶ b') (he : e' ≫ e = 𝟙 b)
    (x : (D.sheaf V).val.obj (op b)) :
    (D.sheaf V).val.map e'.op ((D.sheaf V).val.map e.op x) = x := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, he, op_id,
    PresheafOfModules.map_id]
  rfl

/-- The comparison `F_V(b) ≅ (glued presheaf)(b.left)`: it is the composite of a restriction
map of `F_V` along an isomorphism of `C/V` with a component of `c_{b.hom}`. -/
noncomputable def thetaInvAppIso {V : C} (b : Over V) :
    (D.sheaf V).val.obj (op b) ≅ D.gluedPresheaf.obj (op b.left) where
  hom := D.thetaInvApp b
  inv := D.thetaApp b
  hom_inv_id := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x ↦ ?_)
    change (D.sheaf V).val.map (sliceHomInv b).op (D.isoAppInv b.hom (top b.left)
        (D.isoApp b.hom (top b.left) ((D.sheaf V).val.map (sliceHom b).op x))) = x
    exact (ConcreteCategory.congr_arg ((D.sheaf V).val.map (sliceHomInv b).op)
        (D.isoAppInv_isoApp_apply b.hom (top b.left)
          ((D.sheaf V).val.map (sliceHom b).op x))).trans
      (D.map_eq_self (sliceHom b) (sliceHomInv b) (sliceHomInv_sliceHom b) x)
  inv_hom_id := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x ↦ ?_)
    change D.isoApp b.hom (top b.left) ((D.sheaf V).val.map (sliceHom b).op
        ((D.sheaf V).val.map (sliceHomInv b).op (D.isoAppInv b.hom (top b.left) x))) = x
    exact (ConcreteCategory.congr_arg (D.isoApp b.hom (top b.left))
        (D.map_eq_self (sliceHomInv b) (sliceHom b) (sliceHom_sliceHomInv b)
          (D.isoAppInv b.hom (top b.left) x))).trans
      (D.isoApp_isoAppInv_apply b.hom (top b.left) x)

/-- **The restriction of the glued presheaf of modules to the slice site `C/V` is `F_V`**, as an
isomorphism of the underlying presheaves of abelian groups. -/
noncomputable def thetaInv (V : C) :
    (D.sheaf V).val.presheaf ≅ (Over.forget V).op ⋙ D.gluedPresheaf.presheaf :=
  NatIso.ofComponents
    (fun b ↦ (forget₂ (ModuleCat.{w} ((R.over V).obj.obj b)) AddCommGrpCat).mapIso
      (D.thetaInvAppIso b.unop))
    fun {b b'} k ↦ by
      ext x
      exact D.thetaInvApp_naturality_apply k.unop x

/-- **The glued presheaf of modules of an absolute glueing datum is a sheaf**: its restriction
to every slice site `C/V` is `F_V`, which is one. -/
theorem isSheaf_gluedPresheaf : Presheaf.IsSheaf J D.gluedPresheaf.presheaf :=
  isSheaf_of_isSheaf_over' J _ fun V ↦
    (Presheaf.isSheaf_of_iso_iff (D.thetaInv V)).mp (D.sheaf V).isSheaf

/-- **The sheaf of modules glued from an absolute glueing datum.** -/
noncomputable def gluedSheaf : SheafOfModules.{w} R :=
  ⟨D.gluedPresheaf, D.isSheaf_gluedPresheaf⟩

/-- The comparison `F_V ≅ (glued sheaf)|_{C/V}` of sheaves of modules on the slice site. -/
noncomputable def thetaSheafIso (V : C) : D.sheaf V ≅ D.gluedSheaf.over V :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun b ↦ D.thetaInvAppIso b.unop) fun {b b'} k ↦ by
      refine ModuleCat.hom_ext
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x ↦ ?_)
      exact D.thetaInvApp_naturality_apply k.unop x)

/-- Restriction of a module to a chart is compatible with the comparison isomorphisms: the
comparison at `j_f b` is the comparison at `b` after the component of `c_f`. -/
lemma thetaInvApp_map_apply {V U : C} (f : V ⟶ U) (b : Over V)
    (x : ((SheafOfModules.overMap R f).obj (D.sheaf U)).val.obj (op b)) :
    ConcreteCategory.hom (D.thetaInvApp ((Over.map f).obj b)) x =
      ConcreteCategory.hom (D.thetaInvApp b) (D.isoApp f b x) := by
  show D.isoApp (b.hom ≫ f) (top b.left)
        ((D.sheaf U).val.map (sliceHom ((Over.map f).obj b)).op x) =
      D.isoApp b.hom (top b.left)
        ((D.sheaf V).val.map (sliceHom b).op (D.isoApp f b x))
  refine ((D.isoApp_map_isoApp_apply f b.hom (sliceHom b) x).trans
    (ConcreteCategory.congr_arg _ ?_)).symm
  exact congrArg (fun (m : (Over.map (b.hom ≫ f)).obj (top b.left) ⟶ (Over.map f).obj b) ↦
    (D.sheaf U).val.map m.op x) (by ext; simp [sliceHom, Over.mapComp])

end ModuleGlueingData

/-! ### The category of absolute glueing data for modules -/

namespace ModuleGlueingData

/-- A morphism of absolute glueing data for sheaves of modules: a compatible family of
morphisms `F_U ⟶ G_U`. -/
@[ext]
structure Hom (D E : ModuleGlueingData.{w} R) where
  /-- the morphism `F_U ⟶ G_U` of sheaves of modules on the slice site `C/U` -/
  app (U : C) : D.sheaf U ⟶ E.sheaf U
  /-- compatibility with the comparison isomorphisms -/
  w {V U : C} (f : V ⟶ U) :
    (SheafOfModules.overMap R f).map (app U) ≫ (E.iso f).hom = (D.iso f).hom ≫ app V

attribute [reassoc] Hom.w

/-- Absolute glueing data for sheaves of modules form a category, a morphism being a family of
morphisms `F_U ⟶ G_U` compatible with the comparison isomorphisms. -/
noncomputable instance : Category (ModuleGlueingData.{w} R) where
  Hom := Hom R
  id D := { app := fun _ ↦ 𝟙 _, w := fun _ ↦ by simp }
  comp α β :=
    { app := fun U ↦ α.app U ≫ β.app U
      w := fun f ↦ by
        rw [CategoryTheory.Functor.map_comp, Category.assoc, Hom.w, ← Category.assoc, Hom.w,
          Category.assoc] }

/-- The identity morphism of an absolute glueing datum is the identity on each slice site. -/
@[simp] lemma id_app (D : ModuleGlueingData.{w} R) (U : C) :
    Hom.app (𝟙 D) U = 𝟙 (D.sheaf U) := rfl

/-- Morphisms of absolute glueing data compose slice site by slice site. -/
@[simp] lemma comp_app {D E F : ModuleGlueingData.{w} R} (α : D ⟶ E) (β : E ⟶ F) (U : C) :
    Hom.app (α ≫ β) U = Hom.app α U ≫ Hom.app β U := rfl

/-- Two morphisms of absolute glueing data that agree on every slice site are equal. -/
@[ext] lemma hom_ext {D E : ModuleGlueingData.{w} R} {α β : D ⟶ E}
    (h : ∀ U, Hom.app α U = Hom.app β U) : α = β :=
  Hom.ext (funext h)

/-- A morphism of absolute glueing data for modules all of whose components are isomorphisms is
an isomorphism. -/
lemma isIso_of_isIso_app {D E : ModuleGlueingData.{w} R} (α : D ⟶ E)
    (h : ∀ U, IsIso (Hom.app α U)) : IsIso α := by
  refine ⟨⟨{ app := fun U ↦ inv (Hom.app α U), w := fun {V U} f ↦ ?_ }, ?_, ?_⟩⟩
  · have hα := Hom.w α f
    rw [IsIso.eq_comp_inv, Category.assoc, ← hα, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  · exact hom_ext R fun U ↦ IsIso.hom_inv_id (Hom.app α U)
  · exact hom_ext R fun U ↦ IsIso.inv_hom_id (Hom.app α U)

end ModuleGlueingData

/-! ### The canonical absolute glueing datum of a sheaf of modules -/

/-- Restricting `M|_{C/U}` along the comparison of iterated slice restriction is, on elements,
the identity: the comparison is the identity of `b.left` on underlying objects. -/
lemma over_val_map_mapComp_apply (M : SheafOfModules.{w} R) {W V U : C} (f : V ⟶ U)
    (g : W ⟶ V) (b : Over W)
    (x : (M.over U).val.obj (op ((Over.map f).obj ((Over.map g).obj b)))) :
    (M.over U).val.map ((Over.mapComp g f).hom.app b).op x = x :=
  Eq.trans rfl (presheafOfModules_map_id_apply M.val (op b.left) x)

/-- The component of the composition comparison at a restriction `M|_{C/U}` is, on elements,
the identity. -/
lemma overMapComp_canonical_apply (M : SheafOfModules.{w} R) {W V U : C} (f : V ⟶ U)
    (g : W ⟶ V) (b : Over W)
    (x : ((SheafOfModules.overMap R f ⋙ SheafOfModules.overMap R g).obj
      (M.over U)).val.obj (op b)) :
    ((overMapComp R f g).hom.app (M.over U)).val.app (op b) x = x :=
  (overMapComp_hom_app_val_app R f g (M.over U) b x).trans
    (over_val_map_mapComp_apply R M f g b x)

/-- The cocycle condition for the family of restrictions of a sheaf of modules to the slice
sites: both ways round reach the restriction to the smallest slice. -/
lemma canonicalModule_cocycle (M : SheafOfModules.{w} R) {W V U : C} (f : V ⟶ U) (g : W ⟶ V) :
    (SheafOfModules.overMap R g).map ((SheafOfModules.overFunctorMap R f).app M).hom ≫
        ((SheafOfModules.overFunctorMap R g).app M).hom =
      (overMapComp R f g).hom.app ((SheafOfModules.overFunctor R U).obj M) ≫
        ((SheafOfModules.overFunctorMap R (g ≫ f)).app M).hom := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun b ↦ ?_)
  refine ModuleCat.hom_ext
    (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x ↦ ?_)
  exact (overMapComp_canonical_apply R M f g b.unop x).symm

/-- **The canonical absolute glueing datum of a sheaf of modules** `M` on `C`: the family of
restrictions `M|_{C/U}` together with the canonical isomorphisms
`j_f^{-1}(M|_{C/U}) ≅ M|_{C/V}`. -/
noncomputable def canonicalModuleGlueingData (M : SheafOfModules.{w} R) :
    ModuleGlueingData.{w} R where
  sheaf U := M.over U
  iso f := (SheafOfModules.overFunctorMap R f).app M
  comp f g := canonicalModule_cocycle R M f g

/-- **The canonical-glueing-data functor** for sheaves of modules. -/
noncomputable def canonicalModuleFunctor :
    SheafOfModules.{w} R ⥤ ModuleGlueingData.{w} R where
  obj M := canonicalModuleGlueingData R M
  map {M N} ψ :=
    { app := fun U ↦ (SheafOfModules.overFunctor R U).map ψ
      w := fun f ↦ by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun b ↦ ?_)
        exact ModuleCat.hom_ext
          (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun _ ↦ rfl) }
  map_id M := ModuleGlueingData.hom_ext R fun U ↦ (SheafOfModules.overFunctor R U).map_id M
  map_comp ψ ψ' :=
    ModuleGlueingData.hom_ext R fun U ↦ (SheafOfModules.overFunctor R U).map_comp ψ ψ'

/-! ### `canonicalModuleFunctor` is fully faithful -/

section FullyFaithful

variable {M N : SheafOfModules.{w} R}
  (α : canonicalModuleGlueingData R M ⟶ canonicalModuleGlueingData R N)

/-- A morphism of canonical glueing data is determined by the values of its components at the
tautological objects: the component of `α_U` at `b` in `C/U` agrees with the component of
`α_{b.left}` at `b.left/b.left`. -/
lemma app_val_app_eq (U : C) (b : Over U) (x : M.val.obj (op b.left)) :
    (ModuleGlueingData.Hom.app α U).val.app (op b) x =
      (ModuleGlueingData.Hom.app α b.left).val.app (op (top b.left)) x := by
  have hw := ConcreteCategory.congr_hom
    (congrArg (fun (φ : (SheafOfModules.overMap R b.hom).obj (M.over U) ⟶ N.over b.left) ↦
      φ.val.app (op (top b.left))) (ModuleGlueingData.Hom.w α b.hom)) x
  have hnat := PresheafOfModules.naturality_apply
    (ModuleGlueingData.Hom.app α U).val (sliceHom b).op x
  have e1 : (M.over U).val.map (sliceHom b).op x = x :=
    presheafOfModules_map_id_apply M.val (op b.left) x
  have e2 : ∀ y, (N.over U).val.map (sliceHom b).op y = y :=
    fun y ↦ presheafOfModules_map_id_apply N.val (op b.left) y
  have hnat' : (ModuleGlueingData.Hom.app α U).val.app
        (op ((Over.map b.hom).obj (top b.left))) x =
      (ModuleGlueingData.Hom.app α U).val.app (op b) x :=
    (ConcreteCategory.congr_arg _ e1.symm).trans (hnat.trans (e2 _))
  exact hnat'.symm.trans hw

/-- The map of sheaves of modules on `C` underlying a morphism of canonical glueing data. -/
noncomputable def ofModuleGlueingHom : M ⟶ N :=
  ⟨{ app := fun X ↦ (ModuleGlueingData.Hom.app α X.unop).val.app (op (top X.unop))
     naturality := fun {X Y} h ↦ by
       refine ModuleCat.hom_ext
         (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x ↦ ?_)
       have hnat := PresheafOfModules.naturality_apply
         (ModuleGlueingData.Hom.app α X.unop).val
         (Over.homMk h.unop (by simp) : Over.mk h.unop ⟶ top X.unop).op x
       exact (app_val_app_eq R α X.unop (Over.mk h.unop) (M.val.map h x)).symm.trans
         hnat }⟩

/-- `ofModuleGlueingHom` is a right inverse of `canonicalModuleFunctor` on morphisms. -/
lemma canonicalModuleFunctor_map_ofModuleGlueingHom :
    (canonicalModuleFunctor R).map (ofModuleGlueingHom R α) = α :=
  ModuleGlueingData.hom_ext R fun U ↦ SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun b ↦ ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x ↦
        (app_val_app_eq R α U b.unop x).symm))

end FullyFaithful

/-- The functor `canonicalModuleFunctor R` is faithful. -/
instance : (canonicalModuleFunctor.{w} R).Faithful where
  map_injective {M N} {_ψ _ψ'} h :=
    SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun b ↦ ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x ↦
        ConcreteCategory.congr_hom
          (congrArg (fun (β : canonicalModuleGlueingData R M ⟶
              canonicalModuleGlueingData R N) ↦
            (ModuleGlueingData.Hom.app β b.unop).val.app (op (top b.unop))) h) x))

/-- The functor `canonicalModuleFunctor R` is full. -/
instance : (canonicalModuleFunctor.{w} R).Full where
  map_surjective α := ⟨ofModuleGlueingHom R α, canonicalModuleFunctor_map_ofModuleGlueingHom R α⟩

/-! ### `canonicalModuleFunctor` is essentially surjective, hence an equivalence -/

section EssSurj

variable (D : ModuleGlueingData.{w} R)

/-- The comparison morphism from an absolute glueing datum for modules to the canonical glueing
datum of the sheaf of modules glued from it. -/
noncomputable def toCanonicalModuleGlueingData :
    D ⟶ canonicalModuleGlueingData R D.gluedSheaf where
  app U := (D.thetaSheafIso U).hom
  w {V U} f := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun b ↦ ?_)
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x ↦ ?_)
    exact D.thetaInvApp_map_apply f b.unop x

/-- The comparison morphism from an absolute glueing datum for modules to the canonical glueing
datum of the sheaf of modules glued from it is an isomorphism. -/
instance : IsIso (toCanonicalModuleGlueingData R D) :=
  ModuleGlueingData.isIso_of_isIso_app R (toCanonicalModuleGlueingData R D) fun U ↦
    inferInstanceAs (IsIso (D.thetaSheafIso U).hom)

end EssSurj

/-- The functor `canonicalModuleFunctor R` is essentially surjective. -/
instance : (canonicalModuleFunctor.{w} R).EssSurj where
  mem_essImage D := ⟨D.gluedSheaf, ⟨(asIso (toCanonicalModuleGlueingData R D)).symm⟩⟩

/-- The functor `canonicalModuleFunctor R` is an equivalence of categories. -/
instance : (canonicalModuleFunctor.{w} R).IsEquivalence where

/-- **Stacks 0GWK with module coefficients.** For a site `C` and a sheaf of rings `R` on it,
with no smallness hypothesis and with sheaves of modules in an arbitrary universe, the category
of sheaves of `R`-modules on `C` is equivalent to the category of absolute glueing data for
sheaves of modules, via the functor sending a sheaf of modules to its canonical absolute
glueing datum. -/
noncomputable def canonicalModuleEquivalence :
    SheafOfModules.{w} R ≌ ModuleGlueingData.{w} R :=
  (canonicalModuleFunctor R).asEquivalence

end Modules

end CategoryTheory.SiteGlueing

end
