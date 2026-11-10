module

public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.BigSiteFpqcSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.CoveringSheafCondition

/-!
# Open subschemes of the objects of a chosen big site

Let `C` be a chosen big `τ`-site over a scheme `T` and let `Y` be an object of `C`. Every open
subscheme `V` of the scheme underlying `Y` is again an object of `C`, by the size bound for open
immersions, and the open immersion `V ⟶ Y` is a morphism of `C`. This module records these
objects and morphisms, and the one property of them that the cohomological arguments of the
chapter use: two opens `V₁, V₂` of `Y` give a **Mayer–Vietoris square** of the site,

`V₁ ∩ V₂ ⟶ V₁, V₂ ⟶ V₁ ∪ V₂`,

a pullback square of monomorphisms whose two lower edges generate a covering sieve. This holds
for each of the five topologies, because every jointly surjective family of open immersions is
a `τ`-covering.

## Main definitions

* `Stacks.Adequate.BigSite.restrictOpen` — the open subscheme `V` of an object `Y` of the site,
  as an object of the site, over `T` through `Y`.
* `Stacks.Adequate.BigSite.restrictOpenHom` — the morphism `V' ⟶ V` induced by a morphism
  `g : Y' ⟶ Y` of the site and opens `V' ⊆ g⁻¹ V`.
* `Stacks.Adequate.BigSite.restrictOpenHomOfLE` and `Stacks.Adequate.BigSite.restrictOpenι` —
  the inclusion of opens `V' ⊆ V` of one object, and the inclusion of an open into the object.
* `Stacks.Adequate.BigSite.restrictOpenSquare` — the Mayer–Vietoris square of two opens.

## Main results

* `Stacks.Adequate.BigSite.isPullback_restrictOpenSquare` — the square is a pullback in the
  site.
* `Stacks.Adequate.BigSite.ofTwoArrows_mem_topology` — its two lower edges cover.
* `Stacks.Adequate.BigSite.restrictOpenMayerVietorisSquare` — the square as a Mayer–Vietoris
  square of the topology of the site.
* `Stacks.Adequate.BigSite.isPullback_sections_restrictOpenSquare` — the sections of a sheaf of
  modules over the four corners form a pullback square of abelian groups.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {T : Scheme.{u}} (C : BigSite τ T)

/-! ### The objects and the morphisms -/

/-- **The open subscheme `V` of an object `Y` of a chosen big site, as an object of the site.**
It is below the cutoff because open immersions do not increase size, and it lies over `T`
through `Y`. -/
public def BigSite.restrictOpen (Y : C.category) (V : Y.left.obj.Opens) : C.category :=
  Over.mk (ObjectProperty.homMk
    (X := (⟨(V : Scheme.{u}), Scheme.size_lt_of_isOpenImmersion V.ι Y.left.property⟩ :
      SchemeBelow C.cutoff)) (V.ι ≫ Y.hom.hom))

/-- The scheme underlying `C.restrictOpen Y V` is the open subscheme `V`. -/
@[simp] public theorem BigSite.restrictOpen_left_obj (Y : C.category) (V : Y.left.obj.Opens) :
    (C.restrictOpen Y V).left.obj = (V : Scheme.{u}) := rfl

/-- **The morphism of open subschemes induced by a morphism of the site.** For `g : Y' ⟶ Y` and
opens `V` of `Y` and `V' ⊆ g⁻¹ V` of `Y'`, the restriction `V' ⟶ V` of `g`. -/
public def BigSite.restrictOpenHom {Y Y' : C.category} (g : Y' ⟶ Y) (V : Y.left.obj.Opens)
    (V' : Y'.left.obj.Opens) (e : V' ≤ g.left.hom ⁻¹ᵁ V) :
    C.restrictOpen Y' V' ⟶ C.restrictOpen Y V :=
  Over.homMk (ObjectProperty.homMk (g.left.hom.resLE V V' e)) (by
    apply ObjectProperty.hom_ext
    change g.left.hom.resLE V V' e ≫ V.ι ≫ Y.hom.hom = V'.ι ≫ Y'.hom.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    exact congrArg (V'.ι ≫ ·) (congrArg (fun k => k.hom) (Over.w g)))

/-- The underlying morphism of schemes of `C.restrictOpenHom` is the restriction of `g`. -/
@[simp] public theorem BigSite.restrictOpenHom_left_hom {Y Y' : C.category} (g : Y' ⟶ Y)
    (V : Y.left.obj.Opens) (V' : Y'.left.obj.Opens) (e : V' ≤ g.left.hom ⁻¹ᵁ V) :
    (C.restrictOpenHom g V V' e).left.hom = g.left.hom.resLE V V' e := rfl

/-- Restrictions of composable morphisms compose. -/
public theorem BigSite.restrictOpenHom_comp {Y Y' Y'' : C.category} (g : Y' ⟶ Y)
    (g' : Y'' ⟶ Y') (V : Y.left.obj.Opens) (V' : Y'.left.obj.Opens)
    (V'' : Y''.left.obj.Opens) (e : V' ≤ g.left.hom ⁻¹ᵁ V) (e' : V'' ≤ g'.left.hom ⁻¹ᵁ V')
    (e'' : V'' ≤ (g' ≫ g).left.hom ⁻¹ᵁ V) :
    C.restrictOpenHom g' V' V'' e' ≫ C.restrictOpenHom g V V' e =
      C.restrictOpenHom (g' ≫ g) V V'' e'' :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.Hom.resLE_comp_resLE _ _ _ _))

/-- The restriction of an identity morphism is the identity. -/
public theorem BigSite.restrictOpenHom_id (Y : C.category) (V : Y.left.obj.Opens)
    (e : V ≤ (𝟙 Y : Y ⟶ Y).left.hom ⁻¹ᵁ V) :
    C.restrictOpenHom (𝟙 Y) V V e = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Scheme.Hom.resLE (𝟙 Y.left.obj) V V e = 𝟙 _
  rw [← cancel_mono V.ι, Scheme.Hom.resLE_comp_ι]
  simp

/-- **The inclusion of opens `V' ⊆ V` of one object of the site.** -/
public def BigSite.restrictOpenHomOfLE (Y : C.category) {V' V : Y.left.obj.Opens} (h : V' ≤ V) :
    C.restrictOpen Y V' ⟶ C.restrictOpen Y V :=
  Over.homMk (ObjectProperty.homMk (Y.left.obj.homOfLE h)) (by
    apply ObjectProperty.hom_ext
    change Y.left.obj.homOfLE h ≫ V.ι ≫ Y.hom.hom = V'.ι ≫ Y.hom.hom
    rw [Scheme.homOfLE_ι_assoc])

/-- The underlying morphism of schemes of `C.restrictOpenHomOfLE` is `Scheme.homOfLE`. -/
@[simp] public theorem BigSite.restrictOpenHomOfLE_left_hom (Y : C.category)
    {V' V : Y.left.obj.Opens} (h : V' ≤ V) :
    (C.restrictOpenHomOfLE Y h).left.hom = Y.left.obj.homOfLE h := rfl

/-- Inclusions of opens compose. -/
@[reassoc (attr := simp)]
public theorem BigSite.restrictOpenHomOfLE_comp (Y : C.category)
    {V'' V' V : Y.left.obj.Opens} (h : V'' ≤ V') (h' : V' ≤ V) :
    C.restrictOpenHomOfLE Y h ≫ C.restrictOpenHomOfLE Y h' =
      C.restrictOpenHomOfLE Y (h.trans h') :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.homOfLE_homOfLE _ h h'))

/-- **The inclusion of an open subscheme into an object of the site.** -/
public def BigSite.restrictOpenι (Y : C.category) (V : Y.left.obj.Opens) :
    C.restrictOpen Y V ⟶ Y :=
  Over.homMk (ObjectProperty.homMk V.ι) rfl

/-- The underlying morphism of schemes of `C.restrictOpenι` is the open immersion. -/
@[simp] public theorem BigSite.restrictOpenι_left_hom (Y : C.category) (V : Y.left.obj.Opens) :
    (C.restrictOpenι Y V).left.hom = V.ι := rfl

/-- Restriction of a morphism commutes with the inclusions of the open subschemes. -/
@[reassoc]
public theorem BigSite.restrictOpenHom_comp_ι {Y Y' : C.category} (g : Y' ⟶ Y)
    (V : Y.left.obj.Opens) (V' : Y'.left.obj.Opens) (e : V' ≤ g.left.hom ⁻¹ᵁ V) :
    C.restrictOpenHom g V V' e ≫ C.restrictOpenι Y V = C.restrictOpenι Y' V' ≫ g :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.Hom.resLE_comp_ι _ _))

/-- The inclusion of opens commutes with the inclusions into the object. -/
@[reassoc (attr := simp)]
public theorem BigSite.restrictOpenHomOfLE_comp_ι (Y : C.category) {V' V : Y.left.obj.Opens}
    (h : V' ≤ V) : C.restrictOpenHomOfLE Y h ≫ C.restrictOpenι Y V = C.restrictOpenι Y V' :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.homOfLE_ι _ h))

/-- Restriction of a morphism commutes with the inclusions of opens. -/
public theorem BigSite.restrictOpenHom_comp_homOfLE {Y Y' : C.category} (g : Y' ⟶ Y)
    {V W : Y.left.obj.Opens} {V' W' : Y'.left.obj.Opens} (hV : V ≤ W) (hV' : V' ≤ W')
    (e : V' ≤ g.left.hom ⁻¹ᵁ V) (e' : W' ≤ g.left.hom ⁻¹ᵁ W) :
    C.restrictOpenHom g V V' e ≫ C.restrictOpenHomOfLE Y hV =
      C.restrictOpenHomOfLE Y' hV' ≫ C.restrictOpenHom g W W' e' := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change g.left.hom.resLE V V' e ≫ Y.left.obj.homOfLE hV =
    Y'.left.obj.homOfLE hV' ≫ g.left.hom.resLE W W' e'
  rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι,
    Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]

/-- The inclusion of the open subscheme `⊤` is an isomorphism of the site: it is one of schemes,
and the forgetful functor to schemes reflects isomorphisms. -/
public theorem BigSite.isIso_restrictOpenι_of_eq_top (Y : C.category) (V : Y.left.obj.Opens)
    (hV : V = ⊤) : IsIso (C.restrictOpenι Y V) := by
  subst hV
  have : IsIso ((C.toOver ⋙ Over.forget T).map (C.restrictOpenι Y ⊤)) :=
    inferInstanceAs (IsIso (Y.left.obj.topIso.hom))
  have : (C.toOver ⋙ Over.forget T).ReflectsIsomorphisms := by
    have : C.toOver.ReflectsIsomorphisms := C.fullyFaithfulToOver.reflectsIsomorphisms
    infer_instance
  exact isIso_of_reflects_iso _ (C.toOver ⋙ Over.forget T)

/-- The forgetful functor from a chosen big site to schemes is faithful. -/
public instance BigSite.faithful_toOver_comp_forget :
    (C.toOver ⋙ Over.forget T).Faithful :=
  Functor.Faithful.comp _ _

/-- A morphism of the site whose underlying morphism of schemes is a monomorphism is a
monomorphism: the forgetful functor to schemes is faithful. -/
public theorem BigSite.mono_of_mono_left_hom {Y Y' : C.category} (g : Y' ⟶ Y)
    [Mono g.left.hom] : Mono g :=
  (C.toOver ⋙ Over.forget T).mono_of_mono_map (inferInstanceAs (Mono g.left.hom))

/-- The inclusion of opens is a monomorphism of the site. -/
public instance BigSite.mono_restrictOpenHomOfLE (Y : C.category) {V' V : Y.left.obj.Opens}
    (h : V' ≤ V) : Mono (C.restrictOpenHomOfLE Y h) :=
  have : Mono (C.restrictOpenHomOfLE Y h).left.hom :=
    inferInstanceAs (Mono (Y.left.obj.homOfLE h))
  C.mono_of_mono_left_hom _

/-! ### The Mayer–Vietoris square of two opens -/

/-- **The Mayer–Vietoris square of two opens `V₁, V₂` of an object of the site**: the inclusions
of `V₁ ∩ V₂` into `V₁` and `V₂`, and of these into `V₁ ∪ V₂`. -/
public def BigSite.restrictOpenSquare (Y : C.category) (V₁ V₂ : Y.left.obj.Opens) :
    Square C.category where
  X₁ := C.restrictOpen Y (V₁ ⊓ V₂)
  X₂ := C.restrictOpen Y V₁
  X₃ := C.restrictOpen Y V₂
  X₄ := C.restrictOpen Y (V₁ ⊔ V₂)
  f₁₂ := C.restrictOpenHomOfLE Y inf_le_left
  f₁₃ := C.restrictOpenHomOfLE Y inf_le_right
  f₂₄ := C.restrictOpenHomOfLE Y le_sup_left
  f₃₄ := C.restrictOpenHomOfLE Y le_sup_right
  fac := by rw [BigSite.restrictOpenHomOfLE_comp, BigSite.restrictOpenHomOfLE_comp]

/-- The forgetful functor from a chosen big site to schemes reflects pullbacks: it is a fully
faithful functor followed by the forgetful functor of a slice, which creates connected limits. -/
public instance BigSite.reflectsPullbacks_toOver_comp_forget :
    ReflectsLimitsOfShape WalkingCospan (C.toOver ⋙ Over.forget T) :=
  inferInstance

/-- **The Mayer–Vietoris square of two opens is a pullback square of the site.** Its image in
schemes is the pullback square of the open subschemes `V₁ ∩ V₂ ⊆ V₁, V₂ ⊆ V₁ ∪ V₂`, and the
forgetful functor reflects pullbacks. -/
public theorem BigSite.isPullback_restrictOpenSquare (Y : C.category) (V₁ V₂ : Y.left.obj.Opens) :
    (C.restrictOpenSquare Y V₁ V₂).IsPullback :=
  IsPullback.of_map (C.toOver ⋙ Over.forget T) (C.restrictOpenSquare Y V₁ V₂).fac
    (isPullback_opens_inf_le (X := Y.left.obj) le_sup_left le_sup_right)

/-- **The two inclusions `V₁, V₂ ⊆ V₁ ∪ V₂` generate a covering sieve of the site**, for each of
the five topologies: they are open immersions, which are `τ`-covering morphisms, and they are
jointly surjective. -/
public theorem BigSite.ofTwoArrows_mem_topology (Y : C.category) (V₁ V₂ : Y.left.obj.Opens) :
    Sieve.ofTwoArrows (C.restrictOpenHomOfLE Y (le_sup_left : V₁ ≤ V₁ ⊔ V₂))
      (C.restrictOpenHomOfLE Y (le_sup_right : V₂ ≤ V₁ ⊔ V₂)) ∈
        C.topology (C.restrictOpen Y (V₁ ⊔ V₂)) := by
  refine sieve_generate_mem_topology_of_coveringMorphismProperty C _ _ (fun j => ?_)
    (fun x => ?_)
  · cases j
    · exact isOpenImmersion_le_coveringMorphismProperty τ _
        (inferInstanceAs (IsOpenImmersion (Y.left.obj.homOfLE (le_sup_left : V₁ ≤ V₁ ⊔ V₂))))
    · exact isOpenImmersion_le_coveringMorphismProperty τ _
        (inferInstanceAs (IsOpenImmersion (Y.left.obj.homOfLE (le_sup_right : V₂ ≤ V₁ ⊔ V₂))))
  · obtain ⟨x, hx⟩ := x
    rcases hx with hx | hx
    · exact ⟨.left, ⟨x, hx⟩, Subtype.ext (Scheme.homOfLE_apply le_sup_left _)⟩
    · exact ⟨.right, ⟨x, hx⟩, Subtype.ext (Scheme.homOfLE_apply le_sup_right _)⟩

/-- Sheaves of sets on a chosen big site admit sheafification: the site is essentially small. -/
public instance BigSite.hasSheafify_type : HasSheafify C.topology (Type u) :=
  have := C.essentiallySmall_category
  hasSheafifyEssentiallySmallSite _ _

/-- **The Mayer–Vietoris square of two opens of an object of the site**, as a Mayer–Vietoris
square of the topology of the site. -/
public abbrev BigSite.restrictOpenMayerVietorisSquare (Y : C.category) (V₁ V₂ : Y.left.obj.Opens) :
    C.topology.MayerVietorisSquare :=
  have : Mono (C.restrictOpenSquare Y V₁ V₂).f₂₄ := C.mono_restrictOpenHomOfLE Y le_sup_left
  have : Mono (C.restrictOpenSquare Y V₁ V₂).f₃₄ := C.mono_restrictOpenHomOfLE Y le_sup_right
  GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback (J := C.topology)
    (C.restrictOpenSquare Y V₁ V₂)
    (C.isPullback_restrictOpenSquare Y V₁ V₂) (C.ofTwoArrows_mem_topology Y V₁ V₂)

/-- **Mayer–Vietoris for the sections of a sheaf of modules over two opens.** The sections over
`V₁ ∪ V₂`, `V₁`, `V₂` and `V₁ ∩ V₂` of a sheaf of modules on the site form a pullback square of
abelian groups. -/
public theorem BigSite.isPullback_sections_restrictOpenSquare
    (G : SheafOfModules.{u} C.structureSheaf) (Y : C.category) (V₁ V₂ : Y.left.obj.Opens) :
    ((C.restrictOpenSquare Y V₁ V₂).op.map G.val.presheaf).IsPullback :=
  (C.restrictOpenMayerVietorisSquare Y V₁ V₂).sheafCondition_of_sheaf
    ((SheafOfModules.toSheaf C.structureSheaf).obj G)

end Stacks.Adequate

end
