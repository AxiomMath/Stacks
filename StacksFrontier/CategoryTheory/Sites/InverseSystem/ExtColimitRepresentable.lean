module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ExtColimitOfFiniteSites
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The `Ext` colimit over a representable first variable

This file feeds the dimension shifting of
`Stacks.WeakSites.ExtColimit.nonempty_isColimit_stdCocone` with its two inputs for a
*representable* first variable, and so proves Stacks 09YP in its `Ext` form over an object of a
level: for an inverse system `D` of sites with finite coverings, colimit site `C`, an object `X`
of the level `i` and a system `F` of abelian sheaves with colimit `colim F` on `C`,

`colim_{A : Over i} Ext^n((A.hom)⁻¹ P, F_{A.left}) = Ext^n(u_i⁻¹ P, colim F)` for every `n`,

where `P` is any abelian sheaf on the level `i` *corepresenting the sections over `X`*: a section
`s` of `P` over `X` such that evaluation at `s` is a bijection `(P ⟶ M) ≃ M(X)` for every `M`
(`IsCorepresentingSection`). The two cases of interest are the free abelian sheaf `ℤ_X^♯` on the
representable presheaf of `X` (`isCorepresentingSection_freeRep`) and, on the **terminal
chart**, the constant sheaf `ℤ` at a terminal object of the level
(`isCorepresentingSection_constantSheaf`), the first variable of Mathlib's
`CategoryTheory.Sheaf.H`.

The argument runs for any first variable `𝒜` carrying *corepresenting sections*
(`CorepSections`): corepresenting sections of every `𝒜_A` over `u_{A.hom}(X)` and of `𝒜_∞` over
`u_i(X)`, carried to one another by the transitions and legs of `𝒜`. Evaluation at them turns the
`Ext⁰` cocone into the cocone of sections of Stacks 09YN, and identifies `𝒜_∞` with the free
abelian sheaf on `u_i(X)`, whose `Ext` into the colimit of a pointwise injective system vanishes in
positive degrees. The pullback first variable of a corepresenting `P` carries such sections, the
images of `s` under the units (`corepSections_pullbackFirstVariable`).

## Main results

* `Stacks.WeakSites.ExtColimit.CorepSections.ext_eq_zero_of_pointwise_injective` — the vanishing
  input: `Ext^{n+1}(𝒜_∞, colim F) = 0` for a pointwise injective system `F`
  (`Stacks.WeakSites.ColimitSiteCohomology.isZero_H'_of_pointwise_injective`).
* `Stacks.WeakSites.ExtColimit.CorepSections.nonempty_isColimit_stdCocone_zero` — the degree-zero
  input: the `Ext⁰` cocone is a colimit, by Stacks 09YN
  (`Stacks.WeakSites.ColimitSiteCohomology.abelianSections_jointlySurjective_and_separated`).
* `Stacks.WeakSites.ExtColimit.CorepSections.nonempty_isColimit_stdCocone` — **every degree**,
  every system.
* `Stacks.WeakSites.ExtColimit.nonempty_isColimit_stdCocone_of_isCorepresentingSection`,
  `Stacks.WeakSites.ExtColimit.nonempty_isColimit_stdCocone_freeRep`,
  `Stacks.WeakSites.ExtColimit.nonempty_isColimit_stdCocone_constantSheaf` — the same for the
  pullback first variable of a corepresenting sheaf, of `ℤ_X^♯`, and of the constant sheaf `ℤ` on
  a level with a terminal object.

## Implementation notes

The section-level computations live in a section without the `Ext` instance arguments of
`Stacks.WeakSites.ExtColimit.pullbackFirstVariable`: every mention of that definition makes
instance search re-derive its `HasExt` arguments, and stating the computations for an abstract
first variable with `CorepSections` keeps each declaration within the default heartbeat budget.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.Sites.InverseSystem

universe v u w w₁ w₂ w₃ w₄ w₅

namespace Stacks.WeakSites.ExtColimit

open InverseSystemOfFiniteSites Stacks.Homology Stacks.WeakSites.ColimitSiteCohomology
  Stacks.Sites.FreeRepresentable

section Corepresenting

/-- A section `s` of an abelian sheaf `P` over `X` **corepresents the sections over `X`** when
evaluation at `s` is a bijection `(P ⟶ M) → M(X)` for every abelian sheaf `M`. -/
def IsCorepresentingSection {𝒞 : Type w₁} [Category.{w₂} 𝒞] {J : GrothendieckTopology 𝒞}
    (P : Sheaf J AddCommGrpCat.{w₃}) (X : 𝒞) (s : P.obj.obj (op X)) : Prop :=
  ∀ M : Sheaf J AddCommGrpCat.{w₃}, Function.Bijective (fun h : P ⟶ M => h.hom.app (op X) s)

/-- Composition of morphisms of abelian sheaves, on sections. -/
theorem sheafHom_comp_apply {𝒞 : Type w₁} [Category.{w₂} 𝒞] {J : GrothendieckTopology 𝒞}
    {P Q R : Sheaf J AddCommGrpCat.{w₃}} (f : P ⟶ Q) (g : Q ⟶ R) (V : 𝒞ᵒᵖ) (x : P.obj.obj V) :
    (f ≫ g).hom.app V x = g.hom.app V (f.hom.app V x) := rfl

/-- **The transpose under an inverse image, on sections**: for `L ⊣ G_*` and `h : L P ⟶ M`, the
transpose `P ⟶ G_* M` sends a section `x` over `X` to the value of `h` on the image of `x` under
the unit. -/
theorem homEquiv_hom_app_apply {𝒜 : Type w₁} {ℬ : Type w₄} [Category.{w₂} 𝒜] [Category.{w₅} ℬ]
    {JA : GrothendieckTopology 𝒜} {JB : GrothendieckTopology ℬ} (G : 𝒜 ⥤ ℬ)
    [G.IsContinuous JA JB] {L : Sheaf JA AddCommGrpCat.{w₃} ⥤ Sheaf JB AddCommGrpCat.{w₃}}
    (adj : L ⊣ G.sheafPushforwardContinuous AddCommGrpCat.{w₃} JA JB)
    {P : Sheaf JA AddCommGrpCat.{w₃}} {M : Sheaf JB AddCommGrpCat.{w₃}} (h : L.obj P ⟶ M)
    {X : 𝒜} (x : P.obj.obj (op X)) :
    (adj.homEquiv P M h).hom.app (op X) x =
      h.hom.app (op (G.obj X)) ((adj.unit.app P).hom.app (op X) x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- **An inverse image of a corepresenting sheaf corepresents the sections over the image
object**, with the image of the section under the unit as its section. -/
theorem IsCorepresentingSection.pullback {𝒜 : Type w₁} {ℬ : Type w₄} [Category.{w₂} 𝒜]
    [Category.{w₅} ℬ] {JA : GrothendieckTopology 𝒜} {JB : GrothendieckTopology ℬ} (G : 𝒜 ⥤ ℬ)
    [G.IsContinuous JA JB] {L : Sheaf JA AddCommGrpCat.{w₃} ⥤ Sheaf JB AddCommGrpCat.{w₃}}
    (adj : L ⊣ G.sheafPushforwardContinuous AddCommGrpCat.{w₃} JA JB)
    {P : Sheaf JA AddCommGrpCat.{w₃}} {X : 𝒜} {s : P.obj.obj (op X)}
    (hs : IsCorepresentingSection P X s) :
    IsCorepresentingSection (L.obj P) (G.obj X) ((adj.unit.app P).hom.app (op X) s) := by
  intro M
  have e : (fun h : L.obj P ⟶ M => h.hom.app (op (G.obj X)) ((adj.unit.app P).hom.app (op X) s)) =
      (fun h : P ⟶ (G.sheafPushforwardContinuous AddCommGrpCat.{w₃} JA JB).obj M =>
        h.hom.app (op X) s) ∘ adj.homEquiv P M := by
    funext h
    exact (homEquiv_hom_app_apply G adj h s).symm
  rw [e]
  exact (hs _).comp (Equiv.bijective _)

/-- **Two sheaves corepresenting the sections over one object are isomorphic.** -/
theorem IsCorepresentingSection.nonempty_iso {𝒞 : Type w₁} [Category.{w₂} 𝒞]
    {J : GrothendieckTopology 𝒞} {P Q : Sheaf J AddCommGrpCat.{w₃}} {X : 𝒞}
    {s : P.obj.obj (op X)} {t : Q.obj.obj (op X)} (hs : IsCorepresentingSection P X s)
    (ht : IsCorepresentingSection Q X t) : Nonempty (P ≅ Q) := by
  obtain ⟨f, hf⟩ := (hs Q).2 t
  have hf' : f.hom.app (op X) s = t := hf
  have : IsIso f := isIso_of_coyoneda_map_bijective f (fun M => by
    have e : (fun h : P ⟶ M => h.hom.app (op X) s) ∘ (fun x : Q ⟶ M => f ≫ x) =
        (fun h : Q ⟶ M => h.hom.app (op X) t) := by
      funext x
      simp only [Function.comp_apply, sheafHom_comp_apply, hf']
    exact ((hs M).of_comp_iff' _).1 (e ▸ ht M))
  exact ⟨asIso f⟩

/-- **The free abelian sheaf `ℤ_U^♯` corepresents the sections over `U`**, with its generator. -/
theorem isCorepresentingSection_freeRep {𝒞 : Type w₁} [SmallCategory 𝒞]
    (J : GrothendieckTopology 𝒞) [HasSheafify J AddCommGrpCat.{w₁}] (U : 𝒞) :
    IsCorepresentingSection (freeRep J U) U (freeRepGen J U) := by
  intro M
  have e : (fun h : freeRep J U ⟶ M => h.hom.app (op U) (freeRepGen J U)) = freeRepEquiv J U M := by
    funext h
    exact (freeRepEquiv_apply J U h).symm
  rw [e]
  exact (freeRepEquiv J U M).bijective

/-- **On the terminal chart, the constant sheaf `ℤ` corepresents the sections over the terminal
object**, with the image of `1` under the unit of `constantSheaf ⊣ Γ(T, -)` as its section. -/
theorem isCorepresentingSection_constantSheaf {𝒞 : Type w₁} [Category.{w₂} 𝒞]
    (J : GrothendieckTopology 𝒞) [HasWeakSheafify J AddCommGrpCat.{w₃}] {T : 𝒞}
    (hT : IsTerminal T) :
    IsCorepresentingSection ((constantSheaf J AddCommGrpCat.{w₃}).obj (AddCommGrpCat.of (ULift ℤ)))
      T (((constantSheafAdj J AddCommGrpCat.{w₃} hT).unit.app (AddCommGrpCat.of (ULift ℤ)))
        (ULift.up 1)) := by
  intro M
  have e : (fun h : (constantSheaf J AddCommGrpCat.{w₃}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ M =>
      h.hom.app (op T) (((constantSheafAdj J AddCommGrpCat.{w₃} hT).unit.app
        (AddCommGrpCat.of (ULift ℤ))) (ULift.up 1))) =
      (AddCommGrpCat.uliftZMultiplesAddEquiv _) ∘
        (constantSheafAdj J AddCommGrpCat.{w₃} hT).homEquiv _ M := by
    funext h
    rw [Function.comp_apply, Adjunction.homEquiv_unit]
    rfl
  rw [e]
  exact (AddCommGrpCat.uliftZMultiplesAddEquiv _).bijective.comp (Equiv.bijective _)

/-- `Ext` out of an object isomorphic to one with vanishing `Ext` vanishes. -/
theorem ext_eq_zero_of_iso {𝒞 : Type w₁} [Category.{w₂} 𝒞] [Abelian 𝒞] [HasExt.{w₃} 𝒞]
    {X Y Z : 𝒞} (e : X ≅ Y) {n : ℕ} (h : Subsingleton (Ext.{w₃} Y Z n)) (y : Ext.{w₃} X Z n) :
    y = 0 := by
  have hy : y = (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp y (zero_add n)) (zero_add n) := by
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  rw [hy, Subsingleton.elim ((Ext.mk₀ e.inv).comp y (zero_add n)) 0, Ext.comp_zero]

/-- Transport along an equality of objects and back is the identity, on sections. -/
theorem presheaf_map_eqToHom_eqToHom_apply {𝒞 : Type w₁} [Category.{w₂} 𝒞]
    (Q : 𝒞ᵒᵖ ⥤ AddCommGrpCat.{w₃}) {V W : 𝒞ᵒᵖ} (h : V = W) (h' : W = V) (x : Q.obj V) :
    Q.map (eqToHom h') (Q.map (eqToHom h) x) = x := by
  subst h
  simp

/-- The zero morphism of abelian sheaves, on sections. -/
theorem sheafHom_zero_apply {𝒞 : Type w₁} [Category.{w₂} 𝒞] {J : GrothendieckTopology 𝒞}
    {P Q : Sheaf J AddCommGrpCat.{w₃}} (V : 𝒞ᵒᵖ) (x : P.obj.obj V) :
    (0 : P ⟶ Q).hom.app V x = 0 := rfl

/-- `Ext.homEquiv₀` inverts `Ext.mk₀`. -/
theorem homEquiv₀_mk₀ {𝒞 : Type w₁} [Category.{w₂} 𝒞] [Abelian 𝒞] [HasExt.{w₃} 𝒞] {Y Z : 𝒞}
    (g : Y ⟶ Z) : Ext.homEquiv₀ (Ext.mk₀ g : Ext.{w₃} Y Z 0) = g :=
  (Ext.mk₀_bijective Y Z).1 (Ext.mk₀_homEquiv₀_apply _)

/-- A degree-zero class carried along an exact functor and conjugated, as a morphism. -/
theorem homEquiv₀_extConj_mapExactFunctor_mk₀ {𝒞 : Type w₁} [Category.{w₂} 𝒞] [Abelian 𝒞]
    [HasExt.{w₃} 𝒞] {𝒟 : Type w₄} [Category.{w₅} 𝒟] [Abelian 𝒟] [HasExt.{w₃} 𝒟]
    (L : 𝒞 ⥤ 𝒟) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {X' Y' : 𝒟} {Y Z : 𝒞} (a : X' ⟶ L.obj Y) (g : Y ⟶ Z) (b : L.obj Z ⟶ Y') :
    Ext.homEquiv₀ (extConj a b ((Ext.mk₀ g : Ext.{w₃} Y Z 0).mapExactFunctor L :
      Ext.{w₃} (L.obj Y) (L.obj Z) 0)) = a ≫ L.map g ≫ b := by
  simp only [extConj, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, homEquiv₀_mk₀]

/-- A degree-zero class carried along an exact functor and conjugated, as a morphism. -/
theorem homEquiv₀_extConj_mapExactFunctor {𝒞 : Type w₁} [Category.{w₂} 𝒞] [Abelian 𝒞]
    [HasExt.{w₃} 𝒞] {𝒟 : Type w₄} [Category.{w₅} 𝒟] [Abelian 𝒟] [HasExt.{w₃} 𝒟]
    (L : 𝒞 ⥤ 𝒟) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {X' Y' : 𝒟} {Y Z : 𝒞} (a : X' ⟶ L.obj Y) (x : Ext.{w₃} Y Z 0) (b : L.obj Z ⟶ Y') :
    Ext.homEquiv₀ (extConj a b (x.mapExactFunctor L : Ext.{w₃} (L.obj Y) (L.obj Z) 0)) =
      a ≫ L.map (Ext.homEquiv₀ x) ≫ b := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective Y Z).2 x
  rw [homEquiv₀_extConj_mapExactFunctor_mk₀, homEquiv₀_mk₀]

/-- `Ext.homEquiv₀` sends `0` to `0`. -/
theorem homEquiv₀_zero {𝒞 : Type w₁} [Category.{w₂} 𝒞] [Abelian 𝒞] [HasExt.{w₃} 𝒞] (Y Z : 𝒞) :
    Ext.homEquiv₀ (0 : Ext.{w₃} Y Z 0) = 0 :=
  map_zero (Ext.addEquiv₀ (X := Y) (Y := Z))

end Corepresenting

section Sections

variable {D : InverseSystemOfFiniteSites.{v, u, max u v w}} {C : Type (max u v w)}
  [SmallCategory C] {uC : ∀ i, D.C i ⥤ C} (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  {K : Precoverage C} [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]

/-- The section of `a⁻¹ Q` over `u_a(Y)` attached to a section `x` of `Q` over `Y`: the image of
`x` under the unit of `a⁻¹ ⊣ a_*`. -/
def unitSection {j k : D.I} (a : k ⟶ j) (Q : Sheaf (D.J j) Ab.{max u v w}) {Y : D.C j}
    (x : Q.obj.obj (op Y)) : ((pb.{v, u, w} D a).obj Q).obj.obj (op ((D.u a).obj Y)) :=
  ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D a).unit.app Q).hom.app (op Y) x

/-- The transpose under the inverse image along a transition, on sections. -/
theorem abelianSheafAdjunction_homEquiv_hom_app_apply {j k : D.I} (a : k ⟶ j)
    {Q : Sheaf (D.J j) Ab.{max u v w}} {M : Sheaf (D.J k) Ab.{max u v w}}
    (h : (pb.{v, u, w} D a).obj Q ⟶ M) {Y : D.C j} (x : Q.obj.obj (op Y)) :
    ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D a).homEquiv Q M h).hom.app (op Y) x =
      h.hom.app (op ((D.u a).obj Y)) (unitSection a Q x) :=
  have := D.continuous a
  homEquiv_hom_app_apply (D.u a) (abelianSheafAdjunction.{v, u, max u v w, max u v w} D a) h x

/-- The inverse transpose under the inverse image along a transition, on the unit sections. -/
theorem abelianSheafAdjunction_homEquiv_symm_hom_app_unitSection {j k : D.I} (a : k ⟶ j)
    {Q : Sheaf (D.J j) Ab.{max u v w}} {M : Sheaf (D.J k) Ab.{max u v w}}
    (φ : Q ⟶ (abelianSheafPushforward.{v, u, max u v w, max u v w} D a).obj M) {Y : D.C j}
    (x : Q.obj.obj (op Y)) :
    (((abelianSheafAdjunction.{v, u, max u v w, max u v w} D a).homEquiv Q M).symm φ).hom.app
      (op ((D.u a).obj Y)) (unitSection a Q x) = φ.hom.app (op Y) x := by
  rw [← abelianSheafAdjunction_homEquiv_hom_app_apply, Equiv.apply_symm_apply]

variable (uC K) in
/-- The section of `u_j⁻¹ Q` over `u_j(Y)` attached to a section `x` of `Q` over `Y`: the image
of `x` under the unit of `u_j⁻¹ ⊣ u_{j,*}`. -/
def colUnitSection (j : D.I) (Q : Sheaf (D.J j) Ab.{max u v w}) {Y : D.C j}
    (x : Q.obj.obj (op Y)) :
    ((colimitPullback.{v, u, w} D uC K j).obj Q).obj.obj (op ((uC j).obj Y)) :=
  ((colimitAdj.{v, u, w} D uC K j).unit.app Q).hom.app (op Y) x

/-- The transpose under the inverse image to the colimit site, on sections. -/
theorem colimitAdj_homEquiv_hom_app_apply (j : D.I) {Q : Sheaf (D.J j) Ab.{max u v w}}
    {M : Sheaf K.toGrothendieck Ab.{max u v w}}
    (h : (colimitPullback.{v, u, w} D uC K j).obj Q ⟶ M) {Y : D.C j} (x : Q.obj.obj (op Y)) :
    ((colimitAdj.{v, u, w} D uC K j).homEquiv Q M h).hom.app (op Y) x =
      h.hom.app (op ((uC j).obj Y)) (colUnitSection uC K j Q x) :=
  homEquiv_hom_app_apply (uC j) (colimitAdj.{v, u, w} D uC K j) h x

/-- The inverse transpose under the inverse image to the colimit site, on the unit sections. -/
theorem colimitAdj_homEquiv_symm_hom_app_colUnitSection (j : D.I)
    {Q : Sheaf (D.J j) Ab.{max u v w}} {M : Sheaf K.toGrothendieck Ab.{max u v w}}
    (φ : Q ⟶ (colimitPushforward.{v, u, w} D uC K j).obj M) {Y : D.C j}
    (x : Q.obj.obj (op Y)) :
    (((colimitAdj.{v, u, w} D uC K j).homEquiv Q M).symm φ).hom.app (op ((uC j).obj Y))
      (colUnitSection uC K j Q x) = φ.hom.app (op Y) x := by
  rw [← colimitAdj_homEquiv_hom_app_apply, Equiv.apply_symm_apply]

variable {i : D.I}

variable (K) in
/-- **Corepresenting sections of a first variable** over an object `X` of the level `i`: a
section of each `𝒜_A` over `u_{A.hom}(X)` and a section of `𝒜_∞` over `u_i(X)`, each
corepresenting the sections over its object (`IsCorepresentingSection`), carried to one another
by the transitions and the legs of `𝒜` in direct-image form. For the pullback first variable of
a sheaf corepresenting the sections over `X` these are the images of its section under the units
(`corepSections_pullbackFirstVariable`). -/
structure CorepSections (𝒜 : FirstVariable.{v, u, w} D uC hu K i) (X : D.C i) where
  /-- The section of `𝒜_A` over `u_{A.hom}(X)`. -/
  sec : ∀ A : Over i, (𝒜.obj A).obj.obj (op ((D.u A.hom).obj X))
  /-- The section of `𝒜_∞` over `u_i(X)`. -/
  top : 𝒜.top.obj.obj (op ((uC i).obj X))
  /-- Each section of `𝒜_A` corepresents the sections over `u_{A.hom}(X)`. -/
  isCorep : ∀ A : Over i, IsCorepresentingSection (𝒜.obj A) ((D.u A.hom).obj X) (sec A)
  /-- The section of `𝒜_∞` corepresents the sections over `u_i(X)`. -/
  isCorep_top : IsCorepresentingSection 𝒜.top ((uC i).obj X) top
  φ_sec : ∀ {A B : Over i} (f : A ⟶ B), (𝒜.φ f).hom.app (op ((D.u B.hom).obj X)) (sec B) =
    (𝒜.obj A).obj.map (eqToHom (congrArg op (uObj_eq D f X))) (sec A)
  lg_sec : ∀ A : Over i, (𝒜.lg A).hom.app (op ((D.u A.hom).obj X)) (sec A) =
    𝒜.top.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu A.hom) X).symm)) top

namespace CorepSections

variable {hu} {𝒜 : FirstVariable.{v, u, w} D uC hu K i} {X : D.C i} (S : CorepSections hu K 𝒜 X)

/-- The transition of the first variable in inverse-image form, on the sections. -/
theorem ψ_sec {A B : Over i} (f : A ⟶ B) :
    (𝒜.ψ f).hom.app (op ((D.u f.left).obj ((D.u B.hom).obj X)))
        (unitSection f.left (𝒜.obj B) (S.sec B)) =
      (𝒜.obj A).obj.map (eqToHom (congrArg op (uObj_eq D f X))) (S.sec A) :=
  (abelianSheafAdjunction_homEquiv_symm_hom_app_unitSection f.left (𝒜.φ f) (S.sec B)).trans
    (S.φ_sec f)

/-- The comparison map of the first variable, on the sections, through any morphism. -/
theorem map_comp_sec {A B : Over i} (f : A ⟶ B) {N : Sheaf (D.J A.left) Ab.{max u v w}}
    (M : (pb.{v, u, w} D f.left).obj (𝒜.obj B) ⟶ N) :
    (𝒜.map f ≫ M).hom.app (op ((D.u f.left).obj ((D.u B.hom).obj X)))
        ((𝒜.obj A).obj.map (eqToHom (congrArg op (uObj_eq D f X))) (S.sec A)) =
      M.hom.app (op ((D.u f.left).obj ((D.u B.hom).obj X)))
        (unitSection f.left (𝒜.obj B) (S.sec B)) :=
  (congrArg ((𝒜.map f ≫ M).hom.app (op ((D.u f.left).obj ((D.u B.hom).obj X))))
    (S.ψ_sec f)).symm.trans
    (congrArg (fun q => q.hom.app (op ((D.u f.left).obj ((D.u B.hom).obj X)))
      (unitSection f.left (𝒜.obj B) (S.sec B))) (IsIso.hom_inv_id_assoc (𝒜.ψ f) M))

/-- The transition of a system applied after an inverse image, on the unit sections. -/
theorem transition_unitSection (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
    {A B : Over i} (f : A ⟶ B) (g : 𝒜.obj B ⟶ F.obj B.left) :
    ((pb.{v, u, w} D f.left).map g ≫ F.map f.left).hom.app
        (op ((D.u f.left).obj ((D.u B.hom).obj X))) (unitSection f.left (𝒜.obj B) (S.sec B)) =
      (transition D F f.left).app (op ((D.u B.hom).obj X))
        (g.hom.app (op ((D.u B.hom).obj X)) (S.sec B)) :=
  (abelianSheafAdjunction_homEquiv_hom_app_apply f.left
      ((pb.{v, u, w} D f.left).map g ≫ F.map f.left) (S.sec B)).symm.trans
    (congrArg (fun q => q.hom.app (op ((D.u B.hom).obj X)) (S.sec B))
      (Adjunction.homEquiv_naturality_left
        (abelianSheafAdjunction.{v, u, max u v w, max u v w} D f.left) g (F.map f.left)))

/-- **The degree-zero transitions on the corepresenting sections**: the transition along
`f : A ⟶ B` of a morphism `g : 𝒜_B ⟶ F_{B.left}`, evaluated at the section over `u_{A.hom}(X)`,
is the transition of the system applied to the value of `g` at the section over `u_{B.hom}(X)`,
up to `u_{A.hom}(X) = u_{f.left}(u_{B.hom}(X))`. -/
theorem sec_transition (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
    {A B : Over i} (f : A ⟶ B) (g : 𝒜.obj B ⟶ F.obj B.left) :
    (F.obj A.left).obj.map (eqToHom (congrArg op (uObj_eq D f X)))
      ((𝒜.map f ≫ (pb.{v, u, w} D f.left).map g ≫ F.map f.left).hom.app
        (op ((D.u A.hom).obj X)) (S.sec A)) =
      (transition D F f.left).app (op ((D.u B.hom).obj X))
        (g.hom.app (op ((D.u B.hom).obj X)) (S.sec B)) :=
  (NatTrans.naturality_apply (𝒜.map f ≫ (pb.{v, u, w} D f.left).map g ≫ F.map f.left).hom
    (eqToHom (congrArg op (uObj_eq D f X))) (S.sec A)).symm.trans
    ((S.map_comp_sec f ((pb.{v, u, w} D f.left).map g ≫ F.map f.left)).trans
      (S.transition_unitSection F f g))

/-- The leg of the first variable in inverse-image form, on the sections. -/
theorem legInv_sec (A : Over i) :
    (𝒜.legInv A).hom.app (op ((uC A.left).obj ((D.u A.hom).obj X)))
        (colUnitSection uC K A.left (𝒜.obj A) (S.sec A)) =
      𝒜.top.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu A.hom) X).symm)) S.top :=
  (colimitAdj_homEquiv_symm_hom_app_colUnitSection A.left (𝒜.lg A) (S.sec A)).trans (S.lg_sec A)

/-- The leg of the first variable in comparison form, on the sections, through any morphism. -/
theorem leg_comp_top (A : Over i) {N : Sheaf K.toGrothendieck Ab.{max u v w}}
    (M : (colimitPullback.{v, u, w} D uC K A.left).obj (𝒜.obj A) ⟶ N) :
    (𝒜.leg A ≫ M).hom.app (op ((uC A.left).obj ((D.u A.hom).obj X)))
        (𝒜.top.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu A.hom) X).symm)) S.top) =
      M.hom.app (op ((uC A.left).obj ((D.u A.hom).obj X)))
        (colUnitSection uC K A.left (𝒜.obj A) (S.sec A)) :=
  (congrArg ((𝒜.leg A ≫ M).hom.app (op ((uC A.left).obj ((D.u A.hom).obj X))))
    (S.legInv_sec A)).symm.trans
    (congrArg (fun q => q.hom.app (op ((uC A.left).obj ((D.u A.hom).obj X)))
      (colUnitSection uC K A.left (𝒜.obj A) (S.sec A))) (IsIso.hom_inv_id_assoc (𝒜.legInv A) M))

/-- The leg of a presentation applied after the inverse image to the colimit site, on the unit
sections. -/
theorem systemLeg_colUnitSection (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
    {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
    (A : Over i) (g : 𝒜.obj A ⟶ F.obj A.left) :
    ((colimitPullback.{v, u, w} D uC K A.left).map g ≫ systemLeg ι A.left).hom.app
        (op ((uC A.left).obj ((D.u A.hom).obj X)))
        (colUnitSection uC K A.left (𝒜.obj A) (S.sec A)) =
      (ι A.left).app (op ((D.u A.hom).obj X)) (g.hom.app (op ((D.u A.hom).obj X)) (S.sec A)) :=
  (colimitAdj_homEquiv_hom_app_apply A.left
      ((colimitPullback.{v, u, w} D uC K A.left).map g ≫ systemLeg ι A.left) (S.sec A)).symm.trans
    (congrArg (fun q => q.hom.app (op ((D.u A.hom).obj X)) (S.sec A))
      ((Adjunction.homEquiv_naturality_left (colimitAdj.{v, u, w} D uC K A.left) g
        (systemLeg ι A.left)).trans
        (congrArg (fun q => g ≫ q) (Equiv.apply_symm_apply
          ((colimitAdj.{v, u, w} D uC K A.left).homEquiv (F.obj A.left) 𝒢) ⟨ι A.left⟩))))

/-- The degree-zero legs on the corepresenting sections, before the final transport. -/
theorem top_leg_aux (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
    {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
    (A : Over i) (g : 𝒜.obj A ⟶ F.obj A.left) :
    𝒢.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu A.hom) X).symm))
      ((𝒜.leg A ≫ (colimitPullback.{v, u, w} D uC K A.left).map g ≫ systemLeg ι A.left).hom.app
        (op ((uC i).obj X)) S.top) =
      (ι A.left).app (op ((D.u A.hom).obj X)) (g.hom.app (op ((D.u A.hom).obj X)) (S.sec A)) :=
  (NatTrans.naturality_apply
    (𝒜.leg A ≫ (colimitPullback.{v, u, w} D uC K A.left).map g ≫ systemLeg ι A.left).hom
    (eqToHom (congrArg op (Functor.congr_obj (hu A.hom) X).symm)) S.top).symm.trans
    ((S.leg_comp_top A ((colimitPullback.{v, u, w} D uC K A.left).map g ≫
      systemLeg ι A.left)).trans (S.systemLeg_colUnitSection F ι A g))

/-- **The degree-zero legs on the corepresenting sections**: the leg at `A` of a morphism
`g : 𝒜_A ⟶ F_{A.left}`, evaluated at the section over `u_i(X)`, is the image under the leg of
the presentation of the value of `g` at the section over `u_{A.hom}(X)`, transported along
`u_{A.left}(u_{A.hom}(X)) = u_i(X)`. -/
theorem top_leg (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
    {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
    (A : Over i) (g : 𝒜.obj A ⟶ F.obj A.left) :
    (𝒜.leg A ≫ (colimitPullback.{v, u, w} D uC K A.left).map g ≫ systemLeg ι A.left).hom.app
        (op ((uC i).obj X)) S.top =
      𝒢.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu A.hom) X)))
        ((ι A.left).app (op ((D.u A.hom).obj X)) (g.hom.app (op ((D.u A.hom).obj X)) (S.sec A))) :=
  (presheaf_map_eqToHom_eqToHom_apply 𝒢.obj
    (congrArg op (Functor.congr_obj (hu A.hom) X).symm)
    (congrArg op (Functor.congr_obj (hu A.hom) X)) _).symm.trans
    (congrArg (𝒢.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu A.hom) X))))
      (S.top_leg_aux F ι A g))

end CorepSections

end Sections

section Representable

variable {D : InverseSystemOfFiniteSites.{v, u, max u v w}} {C : Type (max u v w)}
  [SmallCategory C] {uC : ∀ i, D.C i ⥤ C} (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  {K : Precoverage C} [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
  [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})]
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))

variable {i : D.I}

/-- The degree-zero transition of an `Ext` diagram, as a morphism. -/
theorem homEquiv₀_extTransition (𝒜 : FirstVariable.{v, u, w} D uC hu K i)
    (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D) {A B : Over i} (f : A ⟶ B)
    (x : Ext.{max u v w} (𝒜.obj B) (F.obj B.left) 0) :
    Ext.homEquiv₀ (extTransition 𝒜 F 0 f x) =
      𝒜.map f ≫ (pb.{v, u, w} D f.left).map (Ext.homEquiv₀ x) ≫ F.map f.left := by
  rw [extTransition_apply]
  exact homEquiv₀_extConj_mapExactFunctor (pb.{v, u, w} D f.left) (𝒜.map f) x (F.map f.left)

/-- The degree-zero leg of an `Ext` cocone, as a morphism. -/
theorem homEquiv₀_extLeg (𝒜 : FirstVariable.{v, u, w} D uC hu K i)
    (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
    {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
    (A : Over i) (x : Ext.{max u v w} (𝒜.obj A) (F.obj A.left) 0) :
    Ext.homEquiv₀ (extLeg 𝒜 F ι 0 A x) =
      𝒜.leg A ≫ (colimitPullback.{v, u, w} D uC K A.left).map (Ext.homEquiv₀ x) ≫
        systemLeg ι A.left := by
  rw [extLeg_apply]
  exact homEquiv₀_extConj_mapExactFunctor (colimitPullback.{v, u, w} D uC K A.left) (𝒜.leg A) x
    (systemLeg ι A.left)

variable {hu} {𝒜 : FirstVariable.{v, u, w} D uC hu K i} {X : D.C i}

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})] in
include hobj hhom hhom_inj hK in
/-- **The vanishing input of dimension shifting, for a first variable with corepresenting
sections.** `Ext^{n+1}(𝒜_∞, colim F) = 0` for a pointwise injective system `F`: `𝒜_∞` corepresents
the sections over `u_i(X)`, so it is the free abelian sheaf on the representable presheaf of
`u_i(X)`, and the cohomology of `colim F` over an object vanishes in positive degrees
(`Stacks.WeakSites.ColimitSiteCohomology.isZero_H'_of_pointwise_injective`). -/
theorem CorepSections.ext_eq_zero_of_pointwise_injective (S : CorepSections hu K 𝒜 X)
    (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D) (hF : ∀ j, Injective (F.obj j))
    (n : ℕ) (y : Ext.{max u v w} 𝒜.top
      (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) (n + 1)) : y = 0 := by
  obtain ⟨e⟩ := S.isCorep_top.nonempty_iso
    (isCorepresentingSection_freeRep K.toGrothendieck ((uC i).obj X))
  have hz := isZero_H'_of_pointwise_injective D uC hu hobj hhom hhom_inj K hK F hF _ _
    (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK F) ((uC i).obj X)
    (n + 1) n.succ_pos
  exact ext_eq_zero_of_iso e (AddCommGrpCat.subsingleton_of_isZero hz) y

/-- The degree-zero transitions on the corepresenting sections, for `Ext` classes. -/
theorem CorepSections.sec_extTransition (S : CorepSections hu K 𝒜 X)
    (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D) {A B : Over i} (f : A ⟶ B)
    (x : Ext.{max u v w} (𝒜.obj B) (F.obj B.left) 0) :
    (F.obj A.left).obj.map (eqToHom (congrArg op (uObj_eq D f X)))
      ((Ext.homEquiv₀ (extTransition 𝒜 F 0 f x)).hom.app (op ((D.u A.hom).obj X)) (S.sec A)) =
      (transition D F f.left).app (op ((D.u B.hom).obj X))
        ((Ext.homEquiv₀ x).hom.app (op ((D.u B.hom).obj X)) (S.sec B)) := by
  rw [homEquiv₀_extTransition]
  exact S.sec_transition F f (Ext.homEquiv₀ x)

/-- The degree-zero legs on the corepresenting sections, for `Ext` classes. -/
theorem CorepSections.top_extLeg (S : CorepSections hu K 𝒜 X)
    (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
    {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
    (A : Over i) (x : Ext.{max u v w} (𝒜.obj A) (F.obj A.left) 0) :
    (Ext.homEquiv₀ (extLeg 𝒜 F ι 0 A x)).hom.app (op ((uC i).obj X)) S.top =
      𝒢.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu A.hom) X)))
        ((ι A.left).app (op ((D.u A.hom).obj X))
          ((Ext.homEquiv₀ x).hom.app (op ((D.u A.hom).obj X)) (S.sec A))) := by
  rw [homEquiv₀_extLeg]
  exact S.top_leg F ι A (Ext.homEquiv₀ x)

include hobj hhom hhom_inj hK in
/-- **The degree-zero input of dimension shifting, for a first variable with corepresenting
sections** (Stacks 09YN read through the sections). The `Ext⁰` cocone of every system `F` is a
colimit: `Ext⁰(𝒜_A, F_{A.left}) = F_{A.left}(u_{A.hom}(X))` and `Ext⁰(𝒜_∞, colim F) =
(colim F)(u_i(X))` by evaluation at the sections, and on these groups the cocone is the one of
`Stacks.WeakSites.ColimitSiteCohomology.abelianSections_jointlySurjective_and_separated`. -/
theorem CorepSections.nonempty_isColimit_stdCocone_zero (S : CorepSections hu K 𝒜 X)
    (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D) :
    Nonempty (IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 0 F)) := by
  have : PreservesFilteredColimitsOfSize.{v, max u v} (forget Ab.{max u v w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w, max u v w} _
  obtain ⟨hsurj, hsep⟩ := abelianSections_jointlySurjective_and_separated D uC hu hobj hhom
    hhom_inj K hK F (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F)
    (systemKanUnit D uC hu F)
    (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK F)
  have htop : Function.Injective (fun y : Ext.{max u v w} 𝒜.top
      (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) 0 =>
        (Ext.homEquiv₀ (X := 𝒜.top)
          (Y := systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) y).hom.app
          (op ((uC i).obj X)) S.top) :=
    (S.isCorep_top _).1.comp Ext.homEquiv₀.injective
  have hlev : ∀ A : Over i, Function.Bijective
      (fun y : Ext.{max u v w} (𝒜.obj A) (F.obj A.left) 0 =>
        (Ext.homEquiv₀ (X := 𝒜.obj A) (Y := F.obj A.left) y).hom.app
          (op ((D.u A.hom).obj X)) (S.sec A)) :=
    fun A => (S.isCorep A _).comp Ext.homEquiv₀.bijective
  refine ⟨isColimitOfElementwise _ (fun y => ?_) (fun A x hx => ?_)⟩
  · -- every class at the limit comes from a level
    let y' : Ext.{max u v w} 𝒜.top (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) 0 := y
    obtain ⟨j, a, t, ht⟩ := hsurj i X ((Ext.homEquiv₀ y').hom.app (op ((uC i).obj X)) S.top)
    obtain ⟨x, hx⟩ := (hlev (Over.mk a)).2 t
    refine ⟨op (Over.mk a), x, htop ?_⟩
    exact (S.top_extLeg F (kanLegs hu hobj hhom hhom_inj hK F) (Over.mk a) x).trans
      ((congrArg (fun q => (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F).obj.map
        (eqToHom (congrArg op (Functor.congr_obj (hu a) X)))
          ((systemKanUnit D uC hu F j).app (op ((D.u a).obj X)) q)) hx).trans ht)
  · -- a class at a level vanishing at the limit vanishes at a further level
    let x' : Ext.{max u v w} (𝒜.obj A.unop) (F.obj A.unop.left) 0 := x
    have hx' : extLeg 𝒜 F (kanLegs hu hobj hhom hhom_inj hK F) 0 A.unop x' = 0 := hx
    have h0 := S.top_extLeg F (kanLegs hu hobj hhom hhom_inj hK F) A.unop x'
    have hz : (Ext.homEquiv₀ (0 : Ext.{max u v w} 𝒜.top
        (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) 0)).hom.app
          (op ((uC i).obj X)) S.top = 0 := by
      rw [homEquiv₀_zero]
      rfl
    have h1 := (congrArg (fun y => (Ext.homEquiv₀ (X := 𝒜.top)
      (Y := systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) y).hom.app
        (op ((uC i).obj X)) S.top) hx').symm.trans h0
    have hι : (systemKanUnit D uC hu F A.unop.left).app (op ((D.u A.unop.hom).obj X))
        ((Ext.homEquiv₀ x').hom.app (op ((D.u A.unop.hom).obj X)) (S.sec A.unop)) = 0 :=
      (presheaf_map_eqToHom_eqToHom_apply
        (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F).obj
        _ (congrArg op (Functor.congr_obj (hu A.unop.hom) X)).symm _).symm.trans
        ((congrArg _ (h1.symm.trans hz)).trans (map_zero _))
    obtain ⟨k, b, hb⟩ := hsep i X A.unop.left A.unop.hom _ 0 (hι.trans (map_zero _).symm)
    let f : Over.mk (b ≫ A.unop.hom) ⟶ A.unop := Over.homMk b rfl
    refine ⟨op (Over.mk (b ≫ A.unop.hom)), f.op, ?_⟩
    show extTransition 𝒜 F 0 f x' = 0
    apply (hlev (Over.mk (b ≫ A.unop.hom))).1
    have hT := S.sec_extTransition F f x'
    have hE0 : (Ext.homEquiv₀ (0 : Ext.{max u v w} (𝒜.obj (Over.mk (b ≫ A.unop.hom)))
        (F.obj (Over.mk (b ≫ A.unop.hom)).left) 0)).hom.app
          (op ((D.u (Over.mk (b ≫ A.unop.hom)).hom).obj X))
          (S.sec (Over.mk (b ≫ A.unop.hom))) = 0 := by
      rw [homEquiv₀_zero]
      rfl
    refine ((presheaf_map_eqToHom_eqToHom_apply (F.obj k).obj (congrArg op (uObj_eq D f X))
      (congrArg op (uObj_eq D f X)).symm _).symm.trans ?_).trans hE0.symm
    exact (congrArg ((F.obj k).obj.map (eqToHom (congrArg op (uObj_eq D f X)).symm))
      (hT.trans (hb.trans (map_zero _)))).trans (map_zero _)

include hobj hhom hhom_inj hK in
/-- **Stacks 09YP in its `Ext` form, every degree, for a first variable with corepresenting
sections over an object `X` of the level `i`.** For every system `F` of abelian sheaves and every
`n`, the cocone `colim_{A : Over i} Ext^n(𝒜_A, F_{A.left}) → Ext^n(𝒜_∞, colim F)` is a colimit:
dimension shifting (`nonempty_isColimit_stdCocone`) fed with
`CorepSections.nonempty_isColimit_stdCocone_zero` and
`CorepSections.ext_eq_zero_of_pointwise_injective`. -/
theorem CorepSections.nonempty_isColimit_stdCocone (S : CorepSections hu K 𝒜 X) (n : ℕ)
    (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D) :
    Nonempty (IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 n F)) :=
  Stacks.WeakSites.ExtColimit.nonempty_isColimit_stdCocone hu hobj hhom hhom_inj hK 𝒜
    (fun F => S.nonempty_isColimit_stdCocone_zero hobj hhom hhom_inj hK F)
    (fun F hF n y => S.ext_eq_zero_of_pointwise_injective hobj hhom hhom_inj hK F hF n y) n F

variable (P : Sheaf (D.J i) Ab.{max u v w}) (X) (s : P.obj.obj (op X))

variable (hu K) in
/-- The section of `(A.hom)⁻¹ P` over `u_{A.hom}(X)` attached to a section `s` of `P` over `X`. -/
def levelSection (A : Over i) :
    ((pullbackFirstVariable D uC hu K P).obj A).obj.obj (op ((D.u A.hom).obj X)) :=
  unitSection A.hom P s

variable (hu K) in
/-- The section of `u_i⁻¹ P` over `u_i(X)` attached to a section `s` of `P` over `X`. -/
def topSection : (pullbackFirstVariable D uC hu K P).top.obj.obj (op ((uC i).obj X)) :=
  colUnitSection uC K i P s

variable (hu) in
/-- The transition of the pullback first variable along `f : A ⟶ B` in direct-image form sends
the section over `u_{B.hom}(X)` to the section over `u_{A.hom}(X)`. -/
theorem φ_levelSection {A B : Over i} (f : A ⟶ B) :
    ((pullbackFirstVariable D uC hu K P).φ f).hom.app (op ((D.u B.hom).obj X))
        (levelSection hu K X P s B) =
      ((pullbackFirstVariable D uC hu K P).obj A).obj.map
        (eqToHom (congrArg op (uObj_eq D f X))) (levelSection hu K X P s A) := by
  have htr := CategoryTheory.PushforwardCocone.homEquiv_transitionPushforward
    (P := fun {A B : Over i} (f : A ⟶ B) =>
      abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left)
    (fun A => abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom)
    (fun f => overPushforwardIso D f) P f
  have h2 := congrArg (fun q => q.hom.app (op X) s) htr
  refine (abelianSheafAdjunction_homEquiv_hom_app_apply B.hom (overTransition D P f) s).symm.trans
    (h2.trans ?_)
  exact ConcreteCategory.congr_hom (overPushforwardIso_inv_app_app f
    ((pb.{v, u, w} D A.hom).obj P) (op X)) (levelSection hu K X P s A)

variable (hu) in
/-- The leg of the pullback first variable in direct-image form sends the section over
`u_{A.hom}(X)` to the section over `u_i(X)`, transported. -/
theorem lg_levelSection (A : Over i) :
    ((pullbackFirstVariable D uC hu K P).lg A).hom.app (op ((D.u A.hom).obj X))
        (levelSection hu K X P s A) =
      (pullbackFirstVariable D uC hu K P).top.obj.map
        (eqToHom (congrArg op (Functor.congr_obj (hu A.hom) X).symm)) (topSection hu K X P s) := by
  have h2 := congrArg (fun q => q.hom.app (op X) s)
    (Equiv.apply_symm_apply ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom).homEquiv
      P ((colimitPushforward.{v, u, w} D uC K A.left).obj
        ((colimitPullback.{v, u, w} D uC K i).obj P)))
      ((colimitAdj.{v, u, w} D uC K i).unit.app P ≫
        (colimitPushforwardCompIso.{v, u, w} D uC hu K A.hom).inv.app
          ((colimitPullback.{v, u, w} D uC K i).obj P)))
  refine (abelianSheafAdjunction_homEquiv_hom_app_apply A.hom (overLeg D uC hu K P A) s).symm.trans
    (h2.trans ?_)
  let := D.continuous A.hom
  exact ConcreteCategory.congr_hom (sheafPushforwardContinuousComp'_inv_app_app (hu A.hom)
    (D.J i) (D.J A.left) K.toGrothendieck ((colimitPullback.{v, u, w} D uC K i).obj P) X)
    (topSection hu K X P s)

variable {P X s}

variable (hu K) in
/-- If `s` corepresents the sections of `P` over `X`, then its image under the unit corepresents
the sections of the level `A` of the pullback first variable over `u_{A.hom}(X)`. -/
theorem isCorepresentingSection_levelSection (hs : IsCorepresentingSection P X s) (A : Over i) :
    IsCorepresentingSection ((pullbackFirstVariable D uC hu K P).obj A) ((D.u A.hom).obj X)
      (levelSection hu K X P s A) := by
  have := D.continuous A.hom
  exact hs.pullback (D.u A.hom) (abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom)

variable (hu K) in
/-- If `s` corepresents the sections of `P` over `X`, then its image under the unit corepresents
the sections of the top of the pullback first variable over `u_i(X)`. -/
theorem isCorepresentingSection_topSection (hs : IsCorepresentingSection P X s) :
    IsCorepresentingSection (pullbackFirstVariable D uC hu K P).top ((uC i).obj X)
      (topSection hu K X P s) :=
  hs.pullback (uC i) (colimitAdj.{v, u, w} D uC K i)

variable (hu K) in
/-- **The corepresenting sections of the pullback first variable** of a sheaf `P` on the level
`i` corepresenting the sections over `X`: the images of its section under the units. -/
def corepSections_pullbackFirstVariable (hs : IsCorepresentingSection P X s) :
    CorepSections hu K (pullbackFirstVariable D uC hu K P) X where
  sec := levelSection hu K X P s
  top := topSection hu K X P s
  isCorep := isCorepresentingSection_levelSection hu K hs
  isCorep_top := isCorepresentingSection_topSection hu K hs
  φ_sec f := φ_levelSection hu X P s f
  lg_sec A := lg_levelSection hu X P s A

include hobj hhom hhom_inj hK in
/-- **Stacks 09YP in its `Ext` form over an object of a level, every degree**, for the pullback
first variable of a sheaf `P` on the level `i` corepresenting the sections over `X`:
`colim_{A : Over i} Ext^n((A.hom)⁻¹ P, F_{A.left}) = Ext^n(u_i⁻¹ P, colim F)` for every system `F`
and every `n`. -/
theorem nonempty_isColimit_stdCocone_of_isCorepresentingSection
    (hs : IsCorepresentingSection P X s) (n : ℕ)
    (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D) :
    Nonempty (IsColimit
      (stdCocone hu hobj hhom hhom_inj hK (pullbackFirstVariable D uC hu K P) n F)) :=
  (corepSections_pullbackFirstVariable hu K hs).nonempty_isColimit_stdCocone hobj hhom hhom_inj
    hK n F

variable (hu) in
include hobj hhom hhom_inj hK in
/-- **The representable case**: the first variable `ℤ_X^♯`, the free abelian sheaf on the
representable presheaf of an object `X` of the level `i`. Every degree, every system. -/
theorem nonempty_isColimit_stdCocone_freeRep (X : D.C i) (n : ℕ)
    (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D) :
    Nonempty (IsColimit (stdCocone hu hobj hhom hhom_inj hK
      (pullbackFirstVariable D uC hu K (freeRep (D.J i) X)) n F)) :=
  nonempty_isColimit_stdCocone_of_isCorepresentingSection hobj hhom hhom_inj hK
    (isCorepresentingSection_freeRep (D.J i) X) n F

variable (hu) in
include hobj hhom hhom_inj hK in
/-- **The terminal chart**: the first variable is the constant sheaf `ℤ` (the first variable of
Mathlib's `CategoryTheory.Sheaf.H`) on a level `i` with a terminal object `T`. Every degree,
every system: `colim_{A : Over i} Ext^n((A.hom)⁻¹ ℤ, F_{A.left}) = Ext^n(u_i⁻¹ ℤ, colim F)`. -/
theorem nonempty_isColimit_stdCocone_constantSheaf {T : D.C i} (hT : IsTerminal T) (n : ℕ)
    (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D) :
    Nonempty (IsColimit (stdCocone hu hobj hhom hhom_inj hK
      (pullbackFirstVariable D uC hu K
        ((constantSheaf (D.J i) AddCommGrpCat.{max u v w}).obj (AddCommGrpCat.of (ULift ℤ))))
      n F)) :=
  nonempty_isColimit_stdCocone_of_isCorepresentingSection hobj hhom hhom_inj hK
    (isCorepresentingSection_constantSheaf (D.J i) hT) n F

end Representable

end Stacks.WeakSites.ExtColimit

end
