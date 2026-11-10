module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# Towards the functorial covering resolution (Tag 02FU)

An open covering `U` of a ringed space `(X, R)` gives an augmented Čech complex of module
sheaves, whose terms are products of the direct images of the restrictions of a module sheaf
`F` to the multiple intersections, whose differential is the alternating sum of restrictions,
and whose augmentation is a quasi-isomorphism. This file builds that complex and its
augmentation, and supplies the existence of homology; the comparison of the terms with the
intrinsic product coordinates, the augmentation as a map out of the single complex, and the
quasi-isomorphism are not proved here.

## Main definitions

* `Stacks.CechTotalComplex.CoveringResolution.infFunctor X W` is intersection with a fixed open
  set, as a functor on the lattice of open sets;
  `Stacks.CechTotalComplex.CoveringResolution.infFunctorLE` is its monotonicity in `W`.
* `Stacks.CechTotalComplex.CoveringResolution.infPushforward X R F W` is the direct image of the
  restriction of the enlarged module sheaf `F` to `W`: its sections on `V` are those of `F` on
  `V ⊓ W`, with scalars restricted from `R(V)`. This is exactly one factor of
  `Stacks.CechTotalComplex.CoveringResolution.cechSections`.
* `Stacks.CechTotalComplex.CoveringResolution.infPushforwardFunctor` and
  `Stacks.CechTotalComplex.CoveringResolution.infPushforwardOpens` make it functorial
  in the module sheaf and contravariantly functorial in the open set, and
  `Stacks.CechTotalComplex.CoveringResolution.cechDiagram` combines the two.
* `Stacks.CechTotalComplex.CoveringResolution.coveringComplex X R U` is the Čech complex of the
  covering with values in these direct images, functorially in the module sheaf, and
  `Stacks.CechTotalComplex.CoveringResolution.coveringAugmentation` is its augmentation by the
  sections over the terminal open set.
* `Stacks.CechTotalComplex.CoveringResolution.coveringTerm X R U F p` is the degree-`p` term,
  indexed by the intersections `cechIntersection X U p s`.
* `Stacks.CechTotalComplex.CoveringResolution` is the structure the source
  lemma asserts to be inhabited.

## Main results

* `Stacks.CechTotalComplex.CoveringResolution.isContinuous_infFunctor`: intersection with a fixed
  open set is a continuous functor for the topology of open sets, so composing a sheaf with it
  gives a sheaf. This is what makes `Stacks.CechTotalComplex.CoveringResolution.infPushforward`
  a sheaf of modules (`Stacks.CechTotalComplex.CoveringResolution.isSheaf_infPushforward`).
* `Stacks.CechTotalComplex.CoveringResolution.hasHomology_of_enlarged`: every cochain complex of
  sheaves of modules in the enlarged universe has homology in every degree. This discharges the
  `hasHomology` field of `CoveringResolution` for any complex whatsoever.
* `Stacks.CechTotalComplex.CoveringResolution.abelianSheafOfModules`: sheaves of modules in a
  universe at least that of the space and of the rings form an abelian category, with the four
  universes still independent. The ambient sheafification instances are obtained through the
  small model of the site of open sets, so no equal-universe hypothesis is imposed.

## Implementation notes

Intersection with a fixed open set is *not* covered by Mathlib's continuity instances: it is
neither `Opens.map` of a continuous map nor the functor of an open embedding, and it is not
representably flat, since the structured arrows over an open set not contained in `W` form an
empty category. Both halves of continuity are therefore proved directly; each is short
because the lattice of open sets is a thin category, so every coherence condition is
`Subsingleton.elim`.

The direct image is built with `PresheafOfModules.pushforward` along the restriction
`R(V) ⟶ R(V ⊓ W)` of ring sections, which puts the scalars in exactly the form
`Stacks.CechTotalComplex.CoveringResolution.cechSections` uses, and makes the underlying
presheaf of abelian groups definitionally the composite with `infFunctor`, which is where the
sheaf condition comes from.

## References

* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
* [Stacks Project, Equation 01EE](https://stacks.math.columbia.edu/tag/01EE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits

universe u v w t z y

namespace Stacks.CechTotalComplex.CoveringResolution

variable (X : TopCat.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})

/-- Enlarge the carriers of a module presheaf, preserving its scalar actions and
restriction maps. -/
noncomputable def uliftPresheaf
    (F : SheafOfModules.{w} R) : PresheafOfModules.{max u v w t} R.obj where
  obj V := ModuleCat.of _ (ULift.{max u v t} (F.val.obj V))
  map f := (ModuleCat.uliftFunctor.{max u v t} _).map (F.val.map f)
  map_id V := by
    ext x
    change ULift.up (F.val.map (𝟙 V) x.down) = x
    simp
    rfl
  map_comp f g := by
    ext x
    change ULift.up (F.val.map (f ≫ g) x.down) = _
    simp
    rfl

/-- The enlarged module presheaf is still a sheaf. -/
noncomputable def uliftSheaf
    (F : SheafOfModules.{w} R) : SheafOfModules.{max u v w t} R where
  val := uliftPresheaf.{u, v, w, t} X R F
  isSheaf := by
    have h := Presheaf.isSheaf_comp_of_isSheaf _ F.val.presheaf
      AddCommGrpCat.uliftFunctor.{max u v t} F.isSheaf
    let e : (uliftPresheaf.{u, v, w, t} X R F).presheaf ≅
        F.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{max u v t} :=
      NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext x; rfl)
    exact (Presheaf.isSheaf_of_iso_iff e).mpr h

/-- Enlargement of module sheaves, functorial in their morphisms. -/
noncomputable def moduleUniverseLift : SheafOfModules.{w} R ⥤ SheafOfModules.{max u v w t} R where
  obj := uliftSheaf.{u, v, w, t} X R
  map φ := ⟨{
    app V := by
      refine ModuleCat.ofHom ?_
      exact {
        toFun := fun x => ⟨φ.val.app V x.down⟩
        map_add' := fun x y => by ext; exact (φ.val.app V).hom.map_add _ _
        map_smul' := fun r x => by ext; exact (φ.val.app V).hom.map_smul _ _ }
    naturality f := by
      ext x
      exact congrArg ULift.up (PresheafOfModules.naturality_apply φ.val f x.down) }⟩
  map_id F := by ext V x; rfl
  map_comp f g := by ext V x; rfl


/-! ### Intersecting with a fixed open set -/

/-- Intersecting with a fixed open set, as a functor on the lattice of open sets. -/
def infFunctor (W : Opens X) : Opens X ⥤ Opens X where
  obj V := V ⊓ W
  map h := homOfLE (inf_le_inf_right W (leOfHom h))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Intersecting with a fixed open set sends covering sieves to covering sieves. -/
theorem coverPreserving_infFunctor (W : Opens X) :
    CoverPreserving (Opens.grothendieckTopology X) (Opens.grothendieckTopology X)
      (infFunctor X W) := by
  constructor
  intro V S hS x hx
  obtain ⟨V', i, hi, hxV'⟩ := hS x hx.1
  exact ⟨(infFunctor X W).obj V', (infFunctor X W).map i,
    ⟨V', i, 𝟙 _, hi, Subsingleton.elim _ _⟩, hxV', hx.2⟩

/-- Intersecting with a fixed open set preserves compatible families of sections. -/
theorem compatiblePreserving_infFunctor (W : Opens X) :
    CompatiblePreserving.{u} (Opens.grothendieckTopology X) (infFunctor X W) := by
  constructor
  intro G Z T x hx Y₁ Y₂ V f₁ f₂ g₁ g₂ hg₁ hg₂ _
  have hV : V ≤ (infFunctor X W).obj (Y₁ ⊓ Y₂) :=
    le_inf (le_inf (f₁.le.trans inf_le_left) (f₂.le.trans inf_le_left))
      (f₁.le.trans inf_le_right)
  have key := hx (homOfLE (inf_le_left : Y₁ ⊓ Y₂ ≤ Y₁)) (homOfLE inf_le_right) hg₁ hg₂
    (Subsingleton.elim _ _)
  rw [Subsingleton.elim f₁
      (homOfLE hV ≫ (infFunctor X W).map (homOfLE (inf_le_left : Y₁ ⊓ Y₂ ≤ Y₁))),
    Subsingleton.elim f₂
      (homOfLE hV ≫ (infFunctor X W).map (homOfLE (inf_le_right : Y₁ ⊓ Y₂ ≤ Y₂)))]
  simp only [op_comp, G.obj.map_comp, types_comp_apply]
  exact congrArg _ key

/-- Intersecting with a fixed open set is a continuous functor for the topology of open
sets. -/
instance isContinuous_infFunctor (W : Opens X) :
    (infFunctor X W).IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology X) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_infFunctor X W)
    (coverPreserving_infFunctor X W)

/-- Restriction of ring sections to the intersection with a fixed open set. -/
def infRestriction (W : Opens X) : R.obj ⟶ (infFunctor X W).op ⋙ R.obj where
  app V := R.obj.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op
  naturality _ _ _ := by
    refine ((R.obj.map_comp _ _).symm.trans ?_).trans (R.obj.map_comp _ _)
    exact congrArg R.obj.map (Subsingleton.elim _ _)

/-- The direct image of the restriction of an enlarged module sheaf to a fixed open set:
its sections on `V` are those of `F` on `V ⊓ W`, with scalars restricted from `R(V)`. -/
noncomputable def infPushforward (F : SheafOfModules.{w} R) (W : Opens X) :
    PresheafOfModules.{max u v w t} R.obj :=
  (PresheafOfModules.pushforward.{max u v w t} (infRestriction X R W)).obj
    (uliftSheaf.{u, v, w, t} X R F).val

/-- The direct image `infPushforward X R F W` is a sheaf. -/
theorem isSheaf_infPushforward (F : SheafOfModules.{w} R) (W : Opens X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (infPushforward.{u, v, w, t} X R F W).presheaf :=
  (infFunctor X W).op_comp_isSheaf_of_isSheaf _ _ _ (uliftSheaf.{u, v, w, t} X R F).isSheaf

variable {ι : Type t} (U : ι → Opens X)

/-- The intersection indexed by a `(p+1)`-tuple of members of the covering. -/
def cechIntersection (p : ℕ) (s : Fin (p + 1) → ι) : Opens X := ⨅ k, U (s k)

/-- Sections of the degree-`p` product of direct images of restrictions. Each factor
carries the `R(V)`-action induced by restriction to its intersection with `V`. -/
noncomputable def cechSections (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X) :
    ModuleCat.{max u v w t} (R.obj.obj (op V)) :=
  ModuleCat.of _ (∀ s : Fin (p + 1) → ι,
    ((ModuleCat.restrictScalars (R.obj.map (homOfLE inf_le_left :
      V ⊓ cechIntersection X U p s ⟶ V).op).hom).obj
        ((uliftSheaf.{u, v, w, t} X R F).val.obj (op (V ⊓ cechIntersection X U p s)))))

/-- Inclusion of a multiple intersection into the intersection with its `j`th index
omitted, also intersected with the open set on which sections are taken. -/
def cechFaceInclusion (p : ℕ) (s : Fin (p + 2) → ι) (j : Fin (p + 2)) (V : Opens X) :
    V ⊓ cechIntersection X U (p + 1) s ⟶
      V ⊓ cechIntersection X U p (s ∘ j.succAbove) :=
  homOfLE (inf_le_inf_left _ (le_iInf fun k => iInf_le (fun a => U (s a)) (j.succAbove k)))

/-- The zero module sheaf exists independently of the universe of its sections. -/
instance sheafOfModulesHasZeroObject : Limits.HasZeroObject (SheafOfModules.{w} R) :=
  Limits.hasZeroObject_of_hasTerminal_object

/-- A module sheaf placed in degree zero has homology, also after enlarging its universe. -/
instance moduleUniverseLift_single_hasHomology (F : SheafOfModules.{w} R) (p : ℕ) :
    ((moduleUniverseLift.{u, v, w, t} X R ⋙ HomologicalComplex.single
      (SheafOfModules.{max u v w t} R) (ComplexShape.up ℕ) 0).obj F).HasHomology p := by
  dsimp only [Functor.comp_obj]
  infer_instance

/-- A functorial augmented covering resolution: a Čech complex of module sheaves with linear
product coordinates, natural in both the open set and the module sheaf, in which the
differential is the alternating sum of restrictions and the augmentation, a
quasi-isomorphism, is the product of the restriction maps. -/
structure _root_.Stacks.CechTotalComplex.CoveringResolution where
  /-- The Čech complex, functorial in the module sheaf. -/
  complex : SheafOfModules.{w} R ⥤ CochainComplex (SheafOfModules.{max u v w t} R) ℕ
  /-- The canonical augmentation is a natural transformation of functors. -/
  augmentation : moduleUniverseLift.{u, v, w, t} X R ⋙
    HomologicalComplex.single (SheafOfModules.{max u v w t} R) (ComplexShape.up ℕ) 0 ⟶ complex
  /-- Linear product coordinates for the sections of every term. -/
  termIso (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X) :
    ((complex.obj F).X p).val.obj (op V) ≅ cechSections X R U F p V
  /-- The coordinates commute with restriction to smaller open sets. -/
  termIso_restriction (F : SheafOfModules.{w} R) (p : ℕ) {V W : Opens X} (h : W ≤ V)
      (x : ((complex.obj F).X p).val.obj (op V)) (s : Fin (p + 1) → ι) :
    (termIso F p W).hom (((complex.obj F).X p).val.map (homOfLE h).op x) s =
      ULift.up (F.val.map (homOfLE (inf_le_inf_right (cechIntersection X U p s) h)).op
        (((termIso F p V).hom x s).down))
  /-- A module morphism acts on the product by its maps on sections. -/
  termIso_naturality {F G : SheafOfModules.{w} R} (φ : F ⟶ G) (p : ℕ) (V : Opens X)
      (x : ((complex.obj F).X p).val.obj (op V)) (s : Fin (p + 1) → ι) :
    (termIso G p V).hom (((complex.map φ).f p).val.app (op V) x) s =
      ULift.up (φ.val.app (op (V ⊓ cechIntersection X U p s))
        (((termIso F p V).hom x s).down))
  /-- Equation 01EE in these same product coordinates. -/
  differential (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X)
      (x : ((complex.obj F).X p).val.obj (op V)) (s : Fin (p + 2) → ι) :
    (termIso F (p + 1) V).hom (((complex.obj F).d p (p + 1)).val.app (op V) x) s =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        ULift.up (F.val.map (cechFaceInclusion X U p s j V).op
          (((termIso F p V).hom x (s ∘ j.succAbove)).down))
  /-- The augmentation is the product of the canonical restriction maps. -/
  augmentation_f_zero (F : SheafOfModules.{w} R) (V : Opens X)
      (x : (((moduleUniverseLift.{u, v, w, t} X R ⋙ HomologicalComplex.single
        (SheafOfModules.{max u v w t} R) (ComplexShape.up ℕ) 0).obj F).X 0).val.obj (op V))
      (s : Fin 1 → ι) :
    (termIso F 0 V).hom (((augmentation.app F).f 0).val.app (op V) x) s =
      ULift.up (F.val.map (homOfLE inf_le_left : V ⊓ cechIntersection X U 0 s ⟶ V).op
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((moduleUniverseLift.{u, v, w, t} X R).obj F)).hom.val.app (op V) x).down))
  /-- The complex admits homology in every degree. -/
  hasHomology (F : SheafOfModules.{w} R) (p : ℕ) : (complex.obj F).HasHomology p
  /-- Every component of the natural augmentation is a quasi-isomorphism. -/
  quasiIso (F : SheafOfModules.{w} R) :
    letI := hasHomology F
    QuasiIso (augmentation.app F)

attribute [instance] CoveringResolution.hasHomology


/-- Functoriality in the module sheaf of the direct image of the restriction. -/
noncomputable def infPushforwardFunctor (W : Opens X) :
    SheafOfModules.{w} R ⥤ SheafOfModules.{max u v w t} R where
  obj F := ⟨infPushforward.{u, v, w, t} X R F W, isSheaf_infPushforward.{u, v, w, t} X R F W⟩
  map φ := ⟨(PresheafOfModules.pushforward.{max u v w t} (infRestriction X R W)).map
    ((moduleUniverseLift.{u, v, w, t} X R).map φ).val⟩
  map_id F := by
    apply SheafOfModules.hom_ext
    simp only [CategoryTheory.Functor.map_id, SheafOfModules.id_val]
    exact CategoryTheory.Functor.map_id _ _
  map_comp φ ψ := by
    apply SheafOfModules.hom_ext
    simp only [CategoryTheory.Functor.map_comp, SheafOfModules.comp_val]
    exact CategoryTheory.Functor.map_comp _ _ _

/-- The degree-`p` term of the Čech complex of `F`: the product, over the `(p+1)`-tuples of
indices, of the direct images of the restrictions of `F` to the corresponding intersections. -/
noncomputable def coveringTerm (F : SheafOfModules.{w} R) (p : ℕ) :
    SheafOfModules.{max u v w t} R :=
  ∏ᶜ fun s : Fin (p + 1) → ι =>
    (infPushforwardFunctor.{u, v, w, t} X R (cechIntersection X U p s)).obj F

/-! ### Homology in the enlarged universe -/

/-- Abelian groups can be sheafified on the site of open sets in any universe at least that
of the space, through the small model of that site. -/
theorem hasSheafify_opens :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u z} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max u z} _ _

/-- Local bijectivity detects the weak equivalences of abelian groups on the site of open
sets, in any universe at least that of the space. -/
theorem wEqualsLocallyBijective_opens :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u z} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u z} _

/-- Sheaves of modules whose sections live in a universe at least that of the space and of
the rings form an abelian category. The universes of the space, the rings, the modules and
the covering index remain independent: the enlargement is what makes the ambient
sheafification available. -/
@[instance_reducible]
noncomputable def abelianSheafOfModules : Abelian (SheafOfModules.{max u v z} R) := by
  let _ := hasSheafify_opens.{u, max v z} X
  let _ := wEqualsLocallyBijective_opens.{u, max v z} X
  infer_instance

/-- **The `hasHomology` field of `CoveringResolution`, unconditionally.** Every cochain
complex of sheaves of modules in the enlarged universe has homology in every degree. -/
theorem hasHomology_of_enlarged (K : CochainComplex (SheafOfModules.{max u v z} R) ℕ)
    (p : ℕ) : K.HasHomology p := by
  let _ := abelianSheafOfModules.{u, v, z} X R
  infer_instance

/-! ### Shrinking the open set -/

/-- Intersecting with a smaller open set, as a natural transformation. -/
def infFunctorLE {W W' : Opens X} (h : W ≤ W') : infFunctor X W ⟶ infFunctor X W' where
  app V := homOfLE (inf_le_inf_left V h)
  naturality _ _ _ := Subsingleton.elim _ _

/-- Restriction of the direct image of a restriction along a shrinking of the open set. -/
noncomputable def infPushforwardRestriction (F : SheafOfModules.{w} R) {W W' : Opens X}
    (h : W ≤ W') : infPushforward.{u, v, w, t} X R F W' ⟶ infPushforward.{u, v, w, t} X R F W :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (NatTrans.op (infFunctorLE X h))
      (uliftSheaf.{u, v, w, t} X R F).val.presheaf)
    (fun V r m => by
      refine ((uliftSheaf.{u, v, w, t} X R F).val.map_smul
        ((NatTrans.op (infFunctorLE X h)).app V) _ m).trans ?_
      refine congrArg (fun ρ => ρ • _) ?_
      have key : R.obj.map (homOfLE (inf_le_left : V.unop ⊓ W' ≤ V.unop)).op ≫
            R.obj.map ((NatTrans.op (infFunctorLE X h)).app V) =
          R.obj.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op :=
        (R.obj.map_comp _ _).symm.trans (congrArg R.obj.map (Subsingleton.elim _ _))
      exact ConcreteCategory.congr_hom key r)

/-- Restriction of a presheaf of modules along an identity morphism is the identity on
sections. -/
theorem map_id_apply (M : PresheafOfModules.{y} R.obj) (V : (Opens X)ᵒᵖ)
    (x : M.obj V) : M.map (𝟙 V) x = x := by
  rw [M.map_id]
  rfl

/-- Restriction along `le_refl W` is the identity. -/
theorem infPushforwardRestriction_refl (F : SheafOfModules.{w} R) (W : Opens X) :
    infPushforwardRestriction.{u, v, w, t} X R F (le_refl W) = 𝟙 _ := by
  ext V x
  change (uliftSheaf.{u, v, w, t} X R F).val.map
    ((infFunctorLE X (le_refl W)).app V.unop).op x = x
  rw [show ((infFunctorLE X (le_refl W)).app V.unop).op = 𝟙 _ from Subsingleton.elim _ _]
  exact map_id_apply X R _ V x

/-- Restriction along `W' ≤ W''` followed by restriction along `W ≤ W'` is restriction along
`W ≤ W''`. -/
theorem infPushforwardRestriction_trans (F : SheafOfModules.{w} R) {W W' W'' : Opens X}
    (h : W ≤ W') (h' : W' ≤ W'') :
    infPushforwardRestriction.{u, v, w, t} X R F h' ≫
        infPushforwardRestriction.{u, v, w, t} X R F h =
      infPushforwardRestriction.{u, v, w, t} X R F (h.trans h') := by
  ext V x
  exact ((uliftSheaf.{u, v, w, t} X R F).val.map_comp_apply
      ((infFunctorLE X h').app V.unop).op ((infFunctorLE X h).app V.unop).op x).symm.trans
    ((uliftSheaf.{u, v, w, t} X R F).val.congr_map_apply (Subsingleton.elim _ _) x)

/-- The Čech diagram of a module sheaf: the open set `W` is sent to the direct image of the
restriction of `F` to `W`, contravariantly in `W`. -/
noncomputable def infPushforwardOpens (F : SheafOfModules.{w} R) :
    (Opens X)ᵒᵖ ⥤ SheafOfModules.{max u v w t} R where
  obj W := (infPushforwardFunctor.{u, v, w, t} X R W.unop).obj F
  map g := ⟨infPushforwardRestriction.{u, v, w, t} X R F (leOfHom g.unop)⟩
  map_id W := SheafOfModules.hom_ext (infPushforwardRestriction_refl.{u, v, w, t} X R F W.unop)
  map_comp _ _ :=
    SheafOfModules.hom_ext (infPushforwardRestriction_trans.{u, v, w, t} X R F _ _).symm

/-! ### The Čech complex of the covering -/

/-- The Čech diagram, functorially in the module sheaf. -/
noncomputable def cechDiagram :
    SheafOfModules.{w} R ⥤ ((Opens X)ᵒᵖ ⥤ SheafOfModules.{max u v w t} R) where
  obj F := infPushforwardOpens.{u, v, w, t} X R F
  map {F G} φ :=
    { app W := (infPushforwardFunctor.{u, v, w, t} X R W.unop).map φ
      naturality := fun {W W'} g => by
        apply SheafOfModules.hom_ext
        ext V x
        exact PresheafOfModules.naturality_apply ((moduleUniverseLift.{u, v, w, t} X R).map φ).val
          ((infFunctorLE X (leOfHom g.unop)).app V.unop).op x }
  map_id F :=
    NatTrans.ext (funext fun W => (infPushforwardFunctor.{u, v, w, t} X R W.unop).map_id F)
  map_comp φ ψ :=
    NatTrans.ext (funext fun W => (infPushforwardFunctor.{u, v, w, t} X R W.unop).map_comp φ ψ)

/-- **The `complex` field of `CoveringResolution`.** The Čech complex of the covering `U`
with values in the direct images of the restrictions of `F`, functorially in `F`. In degree
`p` it is the product, over the `(p+1)`-tuples `s` of indices, of the direct image of the
restriction of `F` to the intersection `cechIntersection X U p s`, and its differential is
the alternating sum of the restrictions along the face maps. -/
noncomputable def coveringComplex :
    SheafOfModules.{w} R ⥤ CochainComplex (SheafOfModules.{max u v w t} R) ℕ :=
  cechDiagram.{u, v, w, t} X R ⋙ cechComplexFunctor U

/-- The intersection `CechComplex.inter U s` of the Čech complex equals
`cechIntersection X U p s`. -/
theorem inter_eq_cechIntersection (p : ℕ) (s : Fin (p + 1) → ι) :
    Stacks.CategoryTheory.CechComplex.inter U s = cechIntersection X U p s :=
  Stacks.CategoryTheory.CechComplex.inter_eq_iInf U s

/-- The Čech augmentation of the covering complex: the map into degree zero from the
sections over the terminal open set, whose composite with the first differential vanishes by
`Stacks.Cohomology.CechZero.aug_comp_d`. -/
noncomputable def coveringAugmentation (F : SheafOfModules.{w} R) :
    (infPushforwardOpens.{u, v, w, t} X R F).obj (op (⊤_ (Opens X))) ⟶
      ((coveringComplex.{u, v, w, t} X R U).obj F).X 0 :=
  Stacks.Cohomology.CechZero.aug U (infPushforwardOpens.{u, v, w, t} X R F) terminalIsTerminal

end Stacks.CechTotalComplex.CoveringResolution

