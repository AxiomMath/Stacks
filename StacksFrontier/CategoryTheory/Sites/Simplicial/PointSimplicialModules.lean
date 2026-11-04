module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.PointSimplicialSite
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModulePairFunctor

/-!
# Sheaves of modules on the constant simplicial site on the point

Let `A` be a cosimplicial commutative ring, and consider the constant simplicial site on the point
with the sheaf of rings `ringSheaf A`. A sheaf of modules on a component is determined by its
sections at the point, and a sheaf of modules on the total site by its sections at the objects
`tot n`. This file records the resulting extensionality and construction principles, the scalar
action on a pushforward along a transition, and the universal property of a cartesian module read
at the point. It builds the quotient modules `n ↦ Aₙ ⧸ Jₙ` of a compatible family of ideals and the
maps between them, and transports morphisms between the components of a cartesian module along
simplex maps.

All names are in the namespace `CategoryTheory.PointSimplicialSite`.

## Main definitions

* `compHomMk`: a linear map of sections at the point, as a morphism of sheaves of modules on a
  component.
* `quotModule`: the sheaf of modules on the total site with sections `Aₙ ⧸ Jₙ` in degree `n`.
* `transportHom`: the morphism between the degree-`n` components of a cartesian module `X` and a
  module `Y` induced by one between their degree-`m` components.
* `quotMap`: the quotient map `Aₙ ⧸ Jₙ ⟶ Aₙ ⧸ J'ₙ` for `J ≤ J'`.

## Main results

* `quotModule_isCartesian`: a quotient module is cartesian as soon as each ideal `Jₙ` is generated
  by the image of `Jₘ` along every simplex map `φ : m ⟶ n`.
* `comp_hom_ext_of_isCartesian`: two morphisms out of the degree-`n` component of a cartesian
  module which agree on the restrictions of the sections of degree `m` along `φ` are equal.
* `transportHom_comp`: transport along a composite of simplex maps is the composite of the
  transports.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.PointSimplicialSite

variable (A : SimplexCategory ⥤ CommRingCat.{u})

noncomputable section

/-- The object of degree `n` of the total site. -/
abbrev tot (n : SimplexCategory) : situation.{u}.totalCategory := ⟨op n, pt⟩

/-- The total-site arrow lying over a simplex map. -/
abbrev totHom {m n : SimplexCategory} (φ : m ⟶ n) : tot.{u} n ⟶ tot.{u} m :=
  ⟨φ.op, 𝟙 _⟩

variable {A}

/-- Morphisms of sheaves of modules on a component are determined by their sections at the
point. -/
theorem comp_hom_ext {n : SimplexCategory}
    {M N : (situation.{u}.componentRingedTopos (ringSheaf A) n).Modules} {f g : M ⟶ N}
    (h : ∀ x : M.val.obj (op pt), f.val.app (op pt) x = g.val.app (op pt) x) : f = g :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext (LinearMap.ext h))

/-- Morphisms of sheaves of modules on the total site are determined by their sections at the
objects `tot n`. -/
theorem tot_hom_ext {M N : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A))}
    {f g : M ⟶ N}
    (h : ∀ n (x : M.val.obj (op (tot n))), f.val.app (op (tot n)) x = g.val.app (op (tot n)) x) :
    f = g :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun ⟨⟨⟨n⟩, ⟨⟨⟩⟩⟩⟩ =>
    ModuleCat.hom_ext (LinearMap.ext (h n))

/-- A linear map of sections at the point is a morphism of sheaves of modules on a component. -/
def compHomMk {n : SimplexCategory}
    {M N : (situation.{u}.componentRingedTopos (ringSheaf A) n).Modules}
    (f : M.val.obj (op pt) →ₗ[(situation.{u}.componentRingedTopos (ringSheaf A) n).O.val.obj
      (op pt)] N.val.obj (op pt)) : M ⟶ N where
  val := PresheafOfModules.homMk
    { app := fun _ => AddCommGrpCat.ofHom f.toAddMonoidHom
      naturality := fun X Y g => by
        obtain rfl : X = Y := Opposite.unop_injective (subsingleton_pt.{u}.elim _ _)
        obtain rfl : g = 𝟙 X :=
          Quiver.Hom.unop_inj ((subsingleton_hom.{u} X.unop X.unop).elim _ _)
        rw [M.val.presheaf.map_id, N.val.presheaf.map_id]
        exact (Category.id_comp _).trans (Category.comp_id _).symm }
    (fun _ r m => f.map_smul r m)

/-- The sections at the point of `compHomMk f` are given by `f`. -/
theorem compHomMk_app {n : SimplexCategory}
    {M N : (situation.{u}.componentRingedTopos (ringSheaf A) n).Modules}
    (f : M.val.obj (op pt) →ₗ[(situation.{u}.componentRingedTopos (ringSheaf A) n).O.val.obj
      (op pt)] N.val.obj (op pt)) (x : M.val.obj (op pt)) :
    (compHomMk f).val.app (op pt) x = f x := rfl

example {m n : SimplexCategory} (φ : m ⟶ n)
    (N : (situation.{u}.componentRingedTopos (ringSheaf A) n).Modules)
    {M : (situation.{u}.componentRingedTopos (ringSheaf A) n).Modules} (h : N ⟶ M)
    (x : N.val.obj (op pt)) :
    ((situation.{u}.transitionRingedToposHom (ringSheaf A) φ).pushforwardModules.map h).val.app
      (op pt) x = h.val.app (op pt) x := rfl

example {m n : SimplexCategory} (φ : m ⟶ n)
    (X : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A)))
    (x : X.val.obj (op (tot m))) :
    (situation.{u}.restrictTransitionModulesApp (ringSheaf A) φ X).val.app (op pt) x =
      X.val.map (totHom φ).op x := rfl

/-- The ring of sections at the point in degree `n`, as the ring over which the modules of the
component are taken. -/
abbrev secRing (n : SimplexCategory) : RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf
    (situation.{u}.componentRingedTopos (ringSheaf A) n).O).val.obj (op pt)

/-- The ring map of the cosimplicial ring, between the rings of sections. -/
abbrev secMap {m n : SimplexCategory} (φ : m ⟶ n) : secRing (A := A) m →+* secRing (A := A) n :=
  (A.map φ).hom

/-- An element of the ring in degree `n`, read in the ring of sections at the point. -/
abbrev toSec {n : SimplexCategory} (a : A.obj n) : secRing (A := A) n := a

/-- The pushforward of modules along a transition. -/
abbrev pf {m n : SimplexCategory} (φ : m ⟶ n)
    (N : (situation.{u}.componentRingedTopos (ringSheaf A) n).Modules) :
    (situation.{u}.componentRingedTopos (ringSheaf A) m).Modules :=
  (situation.{u}.transitionRingedToposHom (ringSheaf A) φ).pushforwardModules.obj N

/-- The scalar action on the sections at the point of a pushforward of modules along a transition
is the action of the target through the ring map of the cosimplicial ring. -/
theorem pushforward_smul {m n : SimplexCategory} (φ : m ⟶ n)
    (N : (situation.{u}.componentRingedTopos (ringSheaf A) n).Modules)
    (r : secRing (A := A) m) (x : (pf φ N).val.obj (op pt)) :
    r • x = (show (pf φ N).val.obj (op pt) from
      (secMap φ r • (show N.val.obj (op pt) from x) : N.val.obj (op pt))) := by
  refine ((situation.{u}.transitionRingedToposHom (ringSheaf A) φ).pushforwardModules_smul N
    (op pt) r x).trans ?_
  have hr : (Sheaf.sectionsFunctor (situation.{u}.componentRingedTopos (ringSheaf A) m).J
      (op pt)).map ((sheafCompose (situation.{u}.componentRingedTopos (ringSheaf A) m).J
        (forget RingCat)).map (situation.{u}.transitionRingedToposHom (ringSheaf A) φ).fSharpRing)
        r = secMap φ r :=
    (congrArg (fun w => (Sheaf.sectionsFunctor (situation.{u}.componentRingedTopos
      (ringSheaf A) m).J (op pt)).map w r)
      (situation.{u}.transitionRingedToposHom_fSharpRing_forget (ringSheaf A) φ)).trans rfl
  rw [hr]
  exact Sheaf.sectionsFunctor_map_moduleSMulHom _ N (op pt) _ x

/-! ### The universal property of a cartesian module, read at the point -/

/-- The adjunction `f_φ^* ⊣ f_{φ,*}` of the transition along `φ`. -/
abbrev adj {m n : SimplexCategory} (φ : m ⟶ n) :=
  (situation.{u}.transitionRingedToposHom (ringSheaf A) φ).pullbackAdjPushforwardModules

/-- Under the adjunction `f_φ^* ⊣ f_{φ,*}`, the fibre transition of `M` along `φ` followed by `h`
corresponds to the restriction of `M` along `φ` followed by `f_{φ,*} h`. -/
theorem homEquiv_transition_comp {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A)))
    {N : (situation.{u}.componentRingedTopos (ringSheaf A) n).Modules}
    (h : situation.{u}.componentModule (ringSheaf A) M n ⟶ N) :
    (adj φ).homEquiv _ _ (situation.{u}.fiberTransitionModules (ringSheaf A) φ M ≫ h) =
      situation.{u}.restrictTransitionModulesApp (ringSheaf A) φ M ≫
        (situation.{u}.transitionRingedToposHom (ringSheaf A) φ).pushforwardModules.map h :=
  (Adjunction.homEquiv_naturality_right (adj φ) _ h).trans
    (congrArg (· ≫ _) (situation.{u}.fiberTransitionModules_adj (ringSheaf A) φ M))

/-- A transition is invertible as soon as every morphism `Mₘ ⟶ f_{φ,*} N` is uniquely of the form
`ρ ≫ f_{φ,*} h`. -/
theorem isIso_fiberTransitionModules_of_bijective {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A)))
    (hM : ∀ N : (situation.{u}.componentRingedTopos (ringSheaf A) n).Modules,
      Function.Bijective (fun h : situation.{u}.componentModule (ringSheaf A) M n ⟶ N =>
        situation.{u}.restrictTransitionModulesApp (ringSheaf A) φ M ≫
          (situation.{u}.transitionRingedToposHom (ringSheaf A) φ).pushforwardModules.map h)) :
    IsIso (situation.{u}.fiberTransitionModules (ringSheaf A) φ M) := by
  refine isIso_of_coyoneda_map_bijective _ (fun N => ?_)
  have e : (fun h => situation.{u}.fiberTransitionModules (ringSheaf A) φ M ≫ h) =
      ((adj φ).homEquiv _ _).symm ∘ (fun h : situation.{u}.componentModule (ringSheaf A) M n ⟶ N =>
        situation.{u}.restrictTransitionModulesApp (ringSheaf A) φ M ≫
          (situation.{u}.transitionRingedToposHom (ringSheaf A) φ).pushforwardModules.map h) := by
    funext h
    exact ((Equiv.symm_apply_eq _).2 (homEquiv_transition_comp φ M h).symm).symm
  rw [e]
  exact ((adj φ).homEquiv _ _).symm.bijective.comp (hM N)

/-! ### Quotient modules -/

section Quotient

variable (A) (J : ∀ n : SimplexCategory, Ideal (A.obj n))
  (hJ : ∀ {m n : SimplexCategory} (φ : m ⟶ n), J m ≤ (J n).comap (A.map φ).hom)

omit J hJ in
/-- The map of quotient rings induced by a ring map `f` is `f`-semilinear. -/
theorem quotientMap_smul {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal R)
    (I' : Ideal S) (h : I ≤ I'.comap f) (r : R) (m : R ⧸ I) :
    Ideal.quotientMap I' f h (r • m) = f r • Ideal.quotientMap I' f h m := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  show Ideal.quotientMap I' f h (Ideal.Quotient.mk I (r * a)) =
    f r • Ideal.quotientMap I' f h (Ideal.Quotient.mk I a)
  rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, map_mul]
  rfl

/-- The cosimplicial abelian group `n ↦ Aₙ ⧸ Jₙ`. -/
def quotFunctor : SimplexCategory ⥤ AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (A.obj n ⧸ J n)
  map φ := AddCommGrpCat.ofHom (Ideal.quotientMap (J _) (A.map φ).hom (hJ φ)).toAddMonoidHom
  map_id n := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ ((A.map (𝟙 n)).hom a) = Ideal.Quotient.mk _ a
    rw [A.map_id]; rfl
  map_comp φ ψ := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ ((A.map (φ ≫ ψ)).hom a) =
      Ideal.Quotient.mk _ ((A.map ψ).hom ((A.map φ).hom a))
    rw [A.map_comp]; rfl

/-- The sheaf of modules on the total site with sections `Aₙ ⧸ Jₙ` in degree `n`. -/
def quotModule : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A)) where
  val := @PresheafOfModules.ofPresheaf _ _ _
    (situation.{u}.totalSimplexDegree.op ⋙ unopUnop SimplexCategory ⋙ quotFunctor A J hJ)
    (fun X => inferInstanceAs (Module (A.obj X.unop.base.unop)
      (A.obj X.unop.base.unop ⧸ J X.unop.base.unop)))
    (fun X Y f r m => quotientMap_smul (R := A.obj X.unop.base.unop)
      (S := A.obj Y.unop.base.unop) (A.map f.unop.base.unop).hom _ _ (hJ _) r m)
  isSheaf := isSheaf_total _

omit hJ in
/-- The class of `1` in degree `n`. -/
abbrev one (n : SimplexCategory) : A.obj n ⧸ J n := Ideal.Quotient.mk _ 1

/-- A morphism out of a component of a quotient module is determined at the point by the image of
the class of `1`. -/
private theorem app_quotient_mk {n : SimplexCategory}
    {P : (situation.{u}.componentRingedTopos (ringSheaf A) n).Modules}
    (h : situation.{u}.componentModule (ringSheaf A) (quotModule A J hJ) n ⟶ P) (a : A.obj n) :
    h.val.app (op pt) (Ideal.Quotient.mk (J n) a) =
      toSec a • h.val.app (op pt) (one A J n) := by
  let Mn := (situation.{u}.componentModule (ringSheaf A) (quotModule A J hJ) n).val.obj (op pt)
  have hb : (show Mn from Ideal.Quotient.mk (J n) a) = toSec a • (show Mn from one A J n) := by
    change _ = Ideal.Quotient.mk (J n) (a * 1); rw [mul_one]
  exact (congrArg _ hb).trans ((h.val.app (op pt)).hom.map_smul _ _)

/-- **Quotient modules are cartesian** as soon as each ideal `Jₙ` is generated by the image of `Jₘ`
along every simplex map `φ : m ⟶ n`. -/
theorem quotModule_isCartesian
    (hJ' : ∀ {m n : SimplexCategory} (φ : m ⟶ n), J n ≤ (J m).map (A.map φ).hom) :
    situation.{u}.IsCartesianModule (ringSheaf A) (quotModule A J hJ) := by
  intro m n φ
  apply isIso_fiberTransitionModules_of_bijective
  intro N
  let Mn := (situation.{u}.componentModule (ringSheaf A) (quotModule A J hJ) n).val.obj (op pt)
  have hρ : ∀ b : A.obj m, (situation.{u}.restrictTransitionModulesApp (ringSheaf A) φ
      (quotModule A J hJ)).val.app (op pt) (Ideal.Quotient.mk (J m) b) =
        (show Mn from Ideal.Quotient.mk (J n) ((A.map φ).hom b)) := fun b => by
    show Ideal.quotientMap (J n) (A.map φ).hom (hJ φ) (Ideal.Quotient.mk (J m) b) = _
    rw [Ideal.quotientMap_mk]
  constructor
  · intro h₁ h₂ heq
    apply comp_hom_ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show A.obj n ⧸ J n from x)
    have e1 := congrArg (fun k => k.val.app (op pt) (one A J m)) heq
    change h₁.val.app (op pt) ((situation.{u}.restrictTransitionModulesApp (ringSheaf A) φ
        (quotModule A J hJ)).val.app (op pt) (one A J m)) =
      h₂.val.app (op pt) ((situation.{u}.restrictTransitionModulesApp (ringSheaf A) φ
        (quotModule A J hJ)).val.app (op pt) (one A J m)) at e1
    rw [hρ, map_one] at e1
    rw [app_quotient_mk A J hJ h₁ a, app_quotient_mk A J hJ h₂ a, e1]
  · intro k
    let v : N.val.obj (op pt) := k.val.app (op pt) (one A J m)
    have hk : ∀ b : A.obj m, k.val.app (op pt) (Ideal.Quotient.mk (J m) b) =
        (show (pf φ N).val.obj (op pt) from (secMap φ b • v : N.val.obj (op pt))) := fun b => by
      exact (app_quotient_mk A J hJ k b).trans (pushforward_smul φ N b _)
    have hv' : ∀ x ∈ (J m).map (A.map φ).hom, toSec x • v = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j', hj', rfl⟩ := hx
        have h0 := hk j'
        have h00 : k.val.app (op pt) (Ideal.Quotient.mk (J m) j') = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem.2 hj']
          exact (k.val.app (op pt)).hom.map_zero
        exact (h0.symm.trans h00 : _)
      | zero => exact zero_smul _ _
      | add x y _ _ hx hy =>
        exact (add_smul (toSec x) (toSec y) v).trans (by rw [hx, hy, add_zero])
      | smul a x _ hx =>
        exact (mul_smul (toSec a) (toSec x) v).trans (by rw [hx, smul_zero])
    have hv : ∀ j ∈ J n, toSec j • v = 0 := fun j hj => hv' j (hJ' φ hj)
    let : Module (A.obj n) (N.val.obj (op pt)) := (N.val.obj (op pt)).isModule
    let h₀ : (A.obj n ⧸ J n) →ₗ[A.obj n] N.val.obj (op pt) :=
      (J n).liftQ (LinearMap.toSpanSingleton (A.obj n) _ v) (fun j hj => by
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
        exact hv j hj)
    let H : situation.{u}.componentModule (ringSheaf A) (quotModule A J hJ) n ⟶ N := compHomMk h₀
    refine ⟨H, ?_⟩
    apply comp_hom_ext
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (show A.obj m ⧸ J m from x)
    refine (congrArg (fun y => H.val.app (op pt) y) (hρ b)).trans ?_
    refine Eq.trans ?_ (hk b).symm
    rfl

end Quotient

/-! ### Uniqueness and existence of maps out of a cartesian module -/

/-- The total-site arrows over simplex maps compose contravariantly:
`totHom φ ≫ totHom ψ = totHom (ψ ≫ φ)`. -/
theorem totHom_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    totHom.{u} φ ≫ totHom ψ = totHom (ψ ≫ φ) := by
  fapply Pseudofunctor.CoGrothendieck.Hom.ext
  · rfl
  · exact (subsingleton_hom.{u} _ _).elim _ _

/-- The restriction maps of a sheaf of modules on the total site are functorial along composites of
simplex maps. -/
theorem map_totHom_comp (M : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A)))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (y : M.val.obj (op (tot l))) :
    M.val.map (totHom (ψ ≫ φ)).op y = M.val.map (totHom φ).op (M.val.map (totHom ψ).op y) := by
  rw [← totHom_comp, op_comp, M.val.map_comp]
  rfl

/-- **Uniqueness.** Two morphisms out of the degree-`n` component of a cartesian module which agree
on the restrictions of the sections of degree `m` along `φ` are equal. -/
theorem comp_hom_ext_of_isCartesian
    {X : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A))}
    (hX : situation.{u}.IsCartesianModule (ringSheaf A) X) {m n : SimplexCategory} (φ : m ⟶ n)
    {N : (situation.{u}.componentRingedTopos (ringSheaf A) n).Modules}
    (h₁ h₂ : situation.{u}.componentModule (ringSheaf A) X n ⟶ N)
    (h : ∀ y : X.val.obj (op (tot m)), h₁.val.app (op pt) (X.val.map (totHom φ).op y) =
      h₂.val.app (op pt) (X.val.map (totHom φ).op y)) : h₁ = h₂ := by
  have e : (adj φ).homEquiv _ _ (situation.{u}.fiberTransitionModules (ringSheaf A) φ X ≫ h₁) =
      (adj φ).homEquiv _ _ (situation.{u}.fiberTransitionModules (ringSheaf A) φ X ≫ h₂) := by
    rw [homEquiv_transition_comp, homEquiv_transition_comp]
    exact comp_hom_ext h
  exact (Iso.cancel_iso_hom_left (@asIso _ _ _ _
    (situation.{u}.fiberTransitionModules (ringSheaf A) φ X) (hX φ)) _ _).1
      (((adj φ).homEquiv _ _).injective e)

/-- **Existence.** A morphism between the degree-`m` components of a cartesian module `X` and a
module `Y` induces, through the transitions, one between their degree-`n` components which commutes
with the restrictions along `φ`. -/
def transportHom {X : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A))}
    (hX : situation.{u}.IsCartesianModule (ringSheaf A) X)
    (Y : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A)))
    {m n : SimplexCategory} (φ : m ⟶ n)
    (p : situation.{u}.componentModule (ringSheaf A) X m ⟶
      situation.{u}.componentModule (ringSheaf A) Y m) :
    situation.{u}.componentModule (ringSheaf A) X n ⟶
      situation.{u}.componentModule (ringSheaf A) Y n :=
  (@asIso _ _ _ _ (situation.{u}.fiberTransitionModules (ringSheaf A) φ X) (hX φ)).inv ≫
    (situation.{u}.componentModulePullback (ringSheaf A) φ).map p ≫
      situation.{u}.fiberTransitionModules (ringSheaf A) φ Y

/-- `transportHom hX Y φ p` commutes with the restrictions along `φ`: on the restriction of a
section `y` of degree `m` it is the restriction of `p y`. -/
theorem transportHom_apply {X : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A))}
    (hX : situation.{u}.IsCartesianModule (ringSheaf A) X)
    (Y : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A)))
    {m n : SimplexCategory} (φ : m ⟶ n)
    (p : situation.{u}.componentModule (ringSheaf A) X m ⟶
      situation.{u}.componentModule (ringSheaf A) Y m) (y : X.val.obj (op (tot m))) :
    (transportHom hX Y φ p).val.app (op pt) (X.val.map (totHom φ).op y) =
      Y.val.map (totHom φ).op (p.val.app (op pt) y) := by
  have e : situation.{u}.fiberTransitionModules (ringSheaf A) φ X ≫ transportHom hX Y φ p =
      (situation.{u}.componentModulePullback (ringSheaf A) φ).map p ≫
        situation.{u}.fiberTransitionModules (ringSheaf A) φ Y :=
    (@asIso _ _ _ _ (situation.{u}.fiberTransitionModules (ringSheaf A) φ X)
      (hX φ)).hom_inv_id_assoc _
  have e' := congrArg ((adj φ).homEquiv _ _) e
  rw [homEquiv_transition_comp] at e'
  have e'' : (adj φ).homEquiv _ _ ((situation.{u}.componentModulePullback (ringSheaf A) φ).map p ≫
        situation.{u}.fiberTransitionModules (ringSheaf A) φ Y) =
      p ≫ situation.{u}.restrictTransitionModulesApp (ringSheaf A) φ Y :=
    (Adjunction.homEquiv_naturality_left (adj φ) p _).trans
      (congrArg (p ≫ ·) (situation.{u}.fiberTransitionModules_adj (ringSheaf A) φ Y))
  exact congrArg (fun k => k.val.app (op pt) y) (e'.trans e'')

/-- Transport along a composite is the composite of the transports. -/
theorem transportHom_comp {X : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A))}
    (hX : situation.{u}.IsCartesianModule (ringSheaf A) X)
    (Y : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A)))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (q : situation.{u}.componentModule (ringSheaf A) X l ⟶
      situation.{u}.componentModule (ringSheaf A) Y l) :
    transportHom hX Y (ψ ≫ φ) q = transportHom hX Y φ (transportHom hX Y ψ q) := by
  apply comp_hom_ext_of_isCartesian hX (ψ ≫ φ)
  intro y
  exact (transportHom_apply hX Y (ψ ≫ φ) q y).trans ((map_totHom_comp Y ψ φ _).trans
    ((congrArg (fun z => Y.val.map (totHom φ).op z) (transportHom_apply hX Y ψ q y).symm).trans
      ((transportHom_apply hX Y φ (transportHom hX Y ψ q) _).symm.trans
        (congrArg (fun z => (transportHom hX Y φ (transportHom hX Y ψ q)).val.app (op pt) z)
          (map_totHom_comp X ψ φ y).symm))))

/-! ### Maps between quotient modules -/

section QuotMap

variable (A) {J J' : ∀ n : SimplexCategory, Ideal (A.obj n)}
  (hJ : ∀ {m n : SimplexCategory} (φ : m ⟶ n), J m ≤ (J n).comap (A.map φ).hom)
  (hJ₂ : ∀ {m n : SimplexCategory} (φ : m ⟶ n), J' m ≤ (J' n).comap (A.map φ).hom)
  (hle : ∀ n, J n ≤ J' n)

/-- The quotient map `Aₙ ⧸ Jₙ ⟶ Aₙ ⧸ J'ₙ` for `J ≤ J'`. -/
def quotMap : quotModule A J hJ ⟶ quotModule A J' hJ₂ where
  val := PresheafOfModules.homMk
    { app := fun X =>
        AddCommGrpCat.ofHom (Ideal.Quotient.factor (hle X.unop.base.unop)).toAddMonoidHom
      naturality := fun X Y f => by
        ext x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }
    (fun X r x => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)

/-- The quotient map sends the class of `a` modulo `Jₙ` to its class modulo `J'ₙ`. -/
theorem quotMap_apply (n : SimplexCategory) (a : A.obj n) :
    (quotMap A hJ hJ₂ hle).val.app (op (tot n)) (Ideal.Quotient.mk (J n) a) =
      Ideal.Quotient.mk (J' n) a := rfl

end QuotMap

end

end CategoryTheory.PointSimplicialSite

end
