module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact

/-!
# Precomposition on the internal hom of sheaves of modules

Let `O_X` be a sheaf of commutative rings on a topological space `X` and let `F₁`, `F`, `G` be
sheaves of `O_X`-modules. A map `β : F₁ ⟶ F` induces, by precomposition on sections, a map

`β^* : SheafHom_{O_X}(F, G) ⟶ SheafHom_{O_X}(F₁, G)`

of internal homs. Stacks 01CO records the existence of this map and the fact that the section
identifications determine it uniquely; this file constructs it, from the characterising data
alone, and proves that it is contravariantly functorial in `β`.

Because the construction takes the internal homs as *characterised* objects rather than as a
particular model, the map it produces is available for any pair of objects satisfying the
characterisation, and `precomp_id` identifies the two internal homs of one pair of modules.

## Main definitions

* `Stacks.SheafOfModules.overSmul`: multiplication by a section of `O_X` over `U`, as an
  endomorphism of the restriction `G|_U`.
* `Stacks.SheafOfModules.overSectionsEquiv`: the sections of `G|_U` on the slice site over `U`
  are the sections of `G` over `U`.
* `Stacks.SheafOfModules.restrictOverHom`: the restriction of a map `F|_U ⟶ G|_U` to a smaller
  open.
* `SheafHom.precomp`: the precomposition map `β^*` of internal homs.

## Main results

* `SheafHom.sectionsEquiv_restrict` and `SheafHom.sectionsEquiv_smul`: the two naturality axioms
  of `SheafHom`, restated as equalities of morphisms of sheaves of modules rather than
  componentwise.
* `SheafHom.eq_of_isPrecomp`: a precomposition map is unique, so `SheafHom.isPrecomp_precomp`
  characterises `SheafHom.precomp`.
* `SheafHom.precomp_id` and `SheafHom.precomp_comp`: contravariant functoriality.

## Implementation notes

The restriction `G|_U` is `SheafOfModules.over`, whose site is the over-category of `U`; the
component of a map `F|_U ⟶ G|_U` at an open `W ≤ U` is its value at the object
`Over.mk (homOfLE hWU)`, definitionally. Because the morphisms of `Opens X` are
proof-irrelevant, that is also the component of a restricted map, so `restrictOverHom_app` holds
by definition and the restriction axiom of `SheafHom` needs no transport.

Compatibility with scalars is phrased through `overSmul` rather than componentwise: a section of
the internal hom is multiplied by `r` exactly when the corresponding map of restrictions is
postcomposed with multiplication by `r`. In that form it composes, which is what makes the
semilinearity of a precomposition map a one-line associativity argument.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}

section OverSmul

variable (G : SheafOfModules.{u} (structureSheaf Rc)) (U : Opens X)

/-- Multiplication by a section `r` of the structure sheaf over `U`, as an endomorphism of the
restriction `G|_U`: on the component at `W ≤ U` it is multiplication by the restriction of `r`
to `W`. It is a morphism of sheaves of modules because the rings of sections are commutative. -/
def overSmul (r : (structureSheaf Rc).obj.obj (op U)) : G.over U ⟶ G.over U := by
  let R := (structureSheaf Rc).over U
  let top : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let res (W : (Over U)ᵒᵖ) : top ⟶ W := (Over.homMk W.unop.hom).op
  let r₀ : R.obj.obj top := r
  let coeff (W : (Over U)ᵒᵖ) : R.obj.obj W := R.obj.map (res W) r₀
  have coeff_natural {W Z : (Over U)ᵒᵖ} (f : W ⟶ Z) : R.obj.map f (coeff W) = coeff Z := by
    dsimp only [coeff]
    calc R.obj.map f (R.obj.map (res W) r₀) = R.obj.map (res W ≫ f) r₀ :=
          (R.obj.map_comp_apply (res W) f r₀).symm
      _ = R.obj.map (res Z) r₀ :=
          congrArg (fun g : top ⟶ Z => R.obj.map g r₀)
            (Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _)))
  let p : (G.over U).val.presheaf ⟶ (G.over U).val.presheaf :=
    { app := fun W => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun x => coeff W • x) (fun x y => smul_add _ _ _))
      naturality := by
        intro W Z f
        ext x
        change coeff Z • (G.over U).val.map f x = (G.over U).val.map f (coeff W • x)
        exact (congrArg (fun c => c • (G.over U).val.map f x) (coeff_natural f)).symm.trans
          ((G.over U).val.map_smul f (coeff W) x).symm }
  exact ⟨PresheafOfModules.homMk p (by
    intro W a x
    change coeff W • (a • x) = a • (coeff W • x)
    rw [smul_smul, smul_smul]
    exact congrArg (· • x) (@mul_comm (Rc.obj.obj (op W.unop.left)) _ (coeff W) a))⟩

/-- The component of `overSmul` at an object of the slice site is multiplication by the
corresponding restriction of the scalar. -/
lemma overSmul_app (r : (structureSheaf Rc).obj.obj (op U)) (W : (Over U)ᵒᵖ)
    (x : (G.over U).val.obj W) :
    (overSmul G U r).val.app W x =
      ((structureSheaf Rc).over U).obj.map
        (show op (Over.mk (𝟙 U)) ⟶ W from (Over.homMk W.unop.hom).op) r • x :=
  rfl

/-- At the terminal object of the slice site, `overSmul` is multiplication by the scalar
itself. -/
lemma overSmul_app_top (r : (structureSheaf Rc).obj.obj (op U)) (x : G.val.obj (op U)) :
    (overSmul G U r).val.app (op (Over.mk (𝟙 U))) x = r • x := by
  let W : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let q : W ⟶ W := (Over.homMk (𝟙 U)).op
  have hq : q = 𝟙 W := Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))
  let x₀ : (G.over U).val.obj W := x
  let r₀ : ((structureSheaf Rc).over U).obj.obj W := r
  show (overSmul G U r).val.app W x₀ = r₀ • x₀
  calc (overSmul G U r).val.app W x₀ = (((structureSheaf Rc).over U).obj.map q r₀) • x₀ :=
        overSmul_app G U r W x₀
    _ = r₀ • x₀ := by
        simp only [hq]
        exact congrArg (· • x₀) ((congrArg (fun f : ((structureSheaf Rc).over U).obj.obj W ⟶
          ((structureSheaf Rc).over U).obj.obj W => f r₀)
            (((structureSheaf Rc).over U).obj.map_id W)).trans (RingCat.id_apply _ r₀))

end OverSmul

section Sections

variable {G : SheafOfModules.{u} (structureSheaf Rc)}

/-- **Sections of a restriction are sections over the open.** A compatible family of sections of
`G|_U` on the slice site over `U` is determined by, and determines, its value at the terminal
object, which is a section of `G` over `U`. -/
def overSectionsEquiv (U : Opens X) : (G.over U).sections ≃ G.val.obj (op U) where
  toFun s := s.val (op (Over.mk (𝟙 U)))
  invFun x := (G.over U).val.sectionsMk (fun V => G.val.map V.unop.hom.op x) (by
    intro V W f
    change G.val.map f.unop.left.op (G.val.map V.unop.hom.op x) = G.val.map W.unop.hom.op x
    rw [← G.val.map_comp_apply]
    congr 1)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    exact s.property (show (op (Over.mk (𝟙 U)) : (Over U)ᵒᵖ) ⟶ V from (Over.homMk V.unop.hom).op)
  right_inv x := by
    change G.val.presheaf.map (𝟙 (op U)) x = x
    rw [G.val.presheaf.map_id]
    rfl

end Sections

section Restrict

variable (F G : SheafOfModules.{u} (structureSheaf Rc))

/-- The restriction of a map `F|_U ⟶ G|_U` to a smaller open `V ≤ U`, read on the slice
sites. -/
def restrictOverHom {U V : Opens X} (hVU : V ≤ U) (f : F.over U ⟶ G.over U) :
    F.over V ⟶ G.over V :=
  ((SheafOfModules.overFunctorMap (structureSheaf Rc) (homOfLE hVU)).app F).inv ≫
    (SheafOfModules.overMap (structureSheaf Rc) (homOfLE hVU)).map f ≫
      ((SheafOfModules.overFunctorMap (structureSheaf Rc) (homOfLE hVU)).app G).hom

/-- The components of a restricted map are the components of the map itself, at the
corresponding objects of the larger slice site. -/
lemma restrictOverHom_app {U V : Opens X} (hVU : V ≤ U) (f : F.over U ⟶ G.over U)
    (W : (Over V)ᵒᵖ) (x : (F.over V).val.obj W) :
    (restrictOverHom F G hVU f).val.app W x = f.val.app ((Over.map (homOfLE hVU)).op.obj W) x :=
  rfl

/-- Restriction of maps of restrictions is natural in the source. -/
lemma restrictOverHom_comp_left {F₁ : SheafOfModules.{u} (structureSheaf Rc)} {U V : Opens X}
    (hVU : V ≤ U) (β : F₁ ⟶ F) (f : F.over U ⟶ G.over U) :
    β.over V ≫ restrictOverHom F G hVU f = restrictOverHom F₁ G hVU (β.over U ≫ f) := by
  ext W y
  rfl

end Restrict

end Stacks.SheafOfModules

namespace SheafHom

open Stacks.SheafOfModules

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
  {F₂ F₁ F G : SheafOfModules.{u} (structureSheaf Rc)}

/-- **The restriction axiom of `SheafHom`, as an equality of morphisms.** Restricting a section
of the internal hom restricts the corresponding map of restrictions. -/
lemma sectionsEquiv_restrict (H : SheafHom Rc F G) {U V : Opens X} (hVU : V ≤ U)
    (s : H.obj.val.obj (op U)) :
    H.sectionsEquiv V (H.obj.val.map (homOfLE hVU).op s) =
      restrictOverHom F G hVU (H.sectionsEquiv U s) := by
  ext W y
  exact (H.restrict_natural hVU s (W := W.unop.left) W.unop.hom.le y).symm

/-- **The scalar axiom of `SheafHom`, as an equality of morphisms.** Multiplying a section of the
internal hom by a scalar postcomposes the corresponding map of restrictions with multiplication
by that scalar. -/
lemma sectionsEquiv_smul (H : SheafHom Rc F G) (U : Opens X)
    (r : (structureSheaf Rc).obj.obj (op U)) (s : H.obj.val.obj (op U)) :
    H.sectionsEquiv U (r • s) = H.sectionsEquiv U s ≫ overSmul G U r := by
  ext W x
  exact (H.smul_natural U r s (W := W.unop.left) W.unop.hom.le x).trans
    (overSmul_app G U r W ((H.sectionsEquiv U s).val.app W x)).symm

/-- **A precomposition map is unique.** Two morphisms of internal homs which both act on
sections by precomposition with `β` are equal: the section identifications are bijective. -/
lemma eq_of_isPrecomp {β : F₁ ⟶ F} {H : SheafHom Rc F G} {H' : SheafHom Rc F₁ G}
    {m m' : H.obj ⟶ H'.obj} (hm : IsPrecomp Rc β H H' m) (hm' : IsPrecomp Rc β H H' m') :
    m = m' := by
  ext U s
  exact (H'.sectionsEquiv U.unop).injective ((hm U.unop s).trans (hm' U.unop s).symm)

/-- **Precomposition on the internal hom.** A map `β : F₁ ⟶ F` of sheaves of modules induces
`β^* : SheafHom_{O_X}(F, G) ⟶ SheafHom_{O_X}(F₁, G)`, acting on sections over every open by
precomposition with the restriction of `β`. -/
def precomp (β : F₁ ⟶ F) (H : SheafHom Rc F G) (H' : SheafHom Rc F₁ G) : H.obj ⟶ H'.obj := by
  let q (U : (Opens X)ᵒᵖ) (s : H.obj.val.obj U) : H'.obj.val.obj (op U.unop) :=
    (H'.sectionsEquiv U.unop).symm (β.over U.unop ≫ H.sectionsEquiv U.unop s)
  have hq_add (U : (Opens X)ᵒᵖ) (s t : H.obj.val.obj U) : q U (s + t) = q U s + q U t := by
    refine Eq.trans (congrArg (H'.sectionsEquiv U.unop).symm
      (Eq.trans (congrArg (β.over U.unop ≫ ·) (map_add (H.sectionsEquiv U.unop) s t))
        (Preadditive.comp_add _ _ _ _ _ _))) ?_
    exact map_add (H'.sectionsEquiv U.unop).symm _ _
  let p : H.obj.val.presheaf ⟶ H'.obj.val.presheaf :=
    { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.mk' (q U) (hq_add U))
      naturality := by
        intro U V f
        ext s
        have hle : V.unop ≤ U.unop := f.unop.le
        have hf : f = (homOfLE hle).op := Subsingleton.elim _ _
        rw [hf]
        change q V (H.obj.val.map (homOfLE hle).op s) =
          H'.obj.val.map (homOfLE hle).op (q U s)
        refine (H'.sectionsEquiv V.unop).injective ?_
        refine Eq.trans ((H'.sectionsEquiv V.unop).apply_symm_apply _) ?_
        refine Eq.trans (congrArg (β.over V.unop ≫ ·) (sectionsEquiv_restrict H hle s)) ?_
        refine Eq.trans (restrictOverHom_comp_left F G hle β (H.sectionsEquiv U.unop s)) ?_
        refine Eq.trans (congrArg (restrictOverHom F₁ G hle)
          ((H'.sectionsEquiv U.unop).apply_symm_apply _).symm) ?_
        exact (sectionsEquiv_restrict H' hle (q U s)).symm }
  exact ⟨PresheafOfModules.homMk p (by
    intro U r s
    change q U (r • s) = r • q U s
    refine (H'.sectionsEquiv U.unop).injective ?_
    refine Eq.trans ((H'.sectionsEquiv U.unop).apply_symm_apply _) ?_
    refine Eq.trans (congrArg (β.over U.unop ≫ ·) (sectionsEquiv_smul H U.unop r s)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ overSmul G U.unop r)
      ((H'.sectionsEquiv U.unop).apply_symm_apply _).symm) ?_
    exact (sectionsEquiv_smul H' U.unop r (q U s)).symm)⟩

/-- `SheafHom.precomp` acts on sections by precomposition, which by `SheafHom.eq_of_isPrecomp`
determines it. -/
lemma isPrecomp_precomp (β : F₁ ⟶ F) (H : SheafHom Rc F G) (H' : SheafHom Rc F₁ G) :
    IsPrecomp Rc β H H' (precomp β H H') := by
  intro U s
  show H'.sectionsEquiv U ((H'.sectionsEquiv U).symm (β.over U ≫ H.sectionsEquiv U s)) = _
  exact (H'.sectionsEquiv U).apply_symm_apply _

/-- The identity induces the identity: precomposition with `𝟙` on the internal hom of one pair
of modules is the identity. -/
lemma precomp_id (H : SheafHom Rc F G) : precomp (𝟙 F) H H = 𝟙 H.obj := by
  refine eq_of_isPrecomp (isPrecomp_precomp (𝟙 F) H H) (fun U s => ?_)
  have h : SheafOfModules.Hom.over (𝟙 F) U = 𝟙 (F.over U) :=
    (SheafOfModules.overFunctor (structureSheaf Rc) U).map_id F
  show H.sectionsEquiv U s = SheafOfModules.Hom.over (𝟙 F) U ≫ H.sectionsEquiv U s
  rw [h, Category.id_comp]

/-- **Precomposition is contravariantly functorial.** -/
lemma precomp_comp (β₁ : F₂ ⟶ F₁) (β₂ : F₁ ⟶ F) (H : SheafHom Rc F G) (H₁ : SheafHom Rc F₁ G)
    (H₂ : SheafHom Rc F₂ G) :
    precomp (β₁ ≫ β₂) H H₂ = precomp β₂ H H₁ ≫ precomp β₁ H₁ H₂ := by
  refine eq_of_isPrecomp (isPrecomp_precomp (β₁ ≫ β₂) H H₂) (fun U s => ?_)
  have h : SheafOfModules.Hom.over (β₁ ≫ β₂) U = β₁.over U ≫ β₂.over U :=
    (SheafOfModules.overFunctor (structureSheaf Rc) U).map_comp β₁ β₂
  refine Eq.trans (isPrecomp_precomp β₁ H₁ H₂ U _) ?_
  refine Eq.trans (congrArg (β₁.over U ≫ ·) (isPrecomp_precomp β₂ H H₁ U s)) ?_
  rw [h, Category.assoc]

end SheafHom

end
