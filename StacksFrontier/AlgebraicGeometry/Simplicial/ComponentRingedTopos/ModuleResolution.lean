module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentRestriction
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransitionCoherence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalIsSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalPullbacks
import StacksCore.Tactic.StacksAttribute

/-!
# The simplicial resolution of the structure sheaf on a ringed simplicial site

Let `S` be a simplicial-site situation and `O` a sheaf of rings on its total site. For each `n`
the component inclusion `g_n` has a lower shriek `g_{n!}` on sheaves of modules, and the images
`g_{n!} O_n` of the component structure sheaves assemble into an alternating-face complex
`… → g_{2!} O_2 → g_{1!} O_1 → g_{0!} O_0` of `O`-modules which resolves `O`.

The complex is produced from an explicit model: restricted to an object `U` of the total site
lying in simplicial degree `m`, the degree-`n` term is the free `O(U)`-module on the simplex maps
`[n] ⟶ [m]`. That model is identified with `g_{n!} O_n` by comparing universal properties —
`Hom(g_{n!} O_n, F) ≃ Γ(C_n, F_n)` from the lower-shriek adjunction of Stacks 0D72, against the
same group computed from freeness — so the identification needs no direct-sum formula. Objectwise
the model is the free module on the standard simplex `Δ[m]`, which Mathlib's extra degeneracy on
`Δ[m]` contracts; whence exactness in positive degrees and at degree zero.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentFreePresheaf`: the explicit model of
  `g_{n!} O_n`, free over `O` on the simplex labels.
* `CategoryTheory.SimplicialSiteSituation.componentFreeMap` and `.componentFreeAugmentation`:
  relabelling along a simplex map, and the map sending every label to `1`.
* `CategoryTheory.SimplicialSiteSituation.componentSections`: sections of a module of the total
  site over a component, by literal restriction.
* `CategoryTheory.SimplicialSiteSituation.SimplicialModuleResolution` and
  `.SimplicialModuleResolutionActual`: the resolution with its differentials, augmentation,
  exactness and component-section universal property pinned to the model; the second has each
  term literally the lower-shriek image of Stacks 0D72.

## Main results

* `CategoryTheory.SimplicialSiteSituation.simplicialModuleResolution`: **Stacks 0D9B**, the
  resolution itself.
* `CategoryTheory.SimplicialSiteSituation.SimplicialModuleResolution.differential_eq_sum_faceMap`:
  its differential is the alternating sum of the canonical face maps.

## Implementation notes

Coefficients sit at the site universe. That is forced by
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriek`, whose existence is available
only there; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleLowerShriek.lean`.

The component-section bijection is pinned by `homSectionsEquiv_apply`, which evaluates it at the
generator labelled by the identity simplex map, and the differential and the augmentation are
pinned by `differential_eq` and `augmentation_eq` through the same `degreeIso`. Without those
three fields the structure would be satisfied by sign-twisted or automorphism-twisted complexes.

Exactness is transported from the objectwise statement in two steps. Objectwise the complex is
the free module on `Δ[m]`, where the extra degeneracy gives a chain homotopy equivalence with
the constant complex. That gives exactness of presheaves of modules, and the forgetful functor
`SheafOfModules.forget` is full, faithful and left exact, so exactness of the sheaf complex is
recovered from it by `exact_of_map_of_exact_next`, which needs the next short complex to be exact
as well — hence the induction runs downwards from the augmentation.

Both cases of the situation are treated: in case (A) the total category is the contravariant
`CoGrothendieck` construction and the component sections of a sheaf extend along the transition
functors because those are morphisms of sites; in case (B) every arrow of the total category
factors through a fibre, which gives the extension directly.

The construction applies to sheaves of possibly noncommutative rings.

## References

* [Stacks Project, Tag 0D9B](https://stacks.math.columbia.edu/tag/0D9B)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u v w

namespace CategoryTheory.SimplicialSiteSituation

/-- On an object of degree `m`, the labels are the simplex maps `n ⟶ m`.
The lift puts these finite labels in the universe of the ring values. -/
public def simplexIndices (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    S.totalCategoryᵒᵖ ⥤ Type v :=
  (totalSimplexDegree S).leftOp ⋙ coyoneda.obj (Opposite.op n) ⋙ uliftFunctor.{v}

/-- Precomposition of simplex labels by `φ`; in particular this gives the
face maps when `φ` is a coface. -/
public def simplexIndicesMap (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    simplexIndices S n ⟶ simplexIndices S m :=
  Functor.whiskerLeft (totalSimplexDegree S).leftOp
    (Functor.whiskerRight (coyoneda.map φ.op) uliftFunctor.{v})

/-- The explicit presheaf underlying `gₙ! Oₙ`: on an object `U` of degree `m`
it is the free `O(U)`-module on the maps `n ⟶ m`. Restriction both restricts the
coefficients and postcomposes the labels with the base map in the total site. -/
public noncomputable def componentFreePresheaf (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory) :
    PresheafOfModules.{u} O.obj :=
  PresheafOfModules.freeObj (simplexIndices.{u, u} S n)

open CategoryTheory.Limits CategoryTheory.Pseudofunctor

attribute [local implicit_reducible] SimplicialSite.totalPseudofunctor
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete totalCategory Quiver.Hom.toLoc
  CoGrothendieck.category CoGrothendieck.categoryStruct CoGrothendieck.ι Cat.str
  Grothendieck.ι Grothendieck.instCategory uliftFunctor componentFunctor component
  simplexIndices totalSimplexDegree componentFreePresheaf PresheafOfModules.freeObj
  ModuleCat.free ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  PresheafOfModules.presheaf


/- `AlgebraicGeometry.RingedSite.locallyBijective_ulift` shares this short name but is a
different statement: it concludes `J.W` of the lifted map, which is available only through
`GrothendieckTopology.WEqualsLocallyBijective`, whereas the conjunction below needs no such
instance; and it lets the hom universe of `C` differ from the object universe while pinning the
lift to the object universe, so neither statement is an instance of the other. -/
private lemma locallyBijective_ulift {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type v} (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallyInjective J (Functor.whiskerRight f uliftFunctor.{w}) ∧
    Presheaf.IsLocallySurjective J (Functor.whiskerRight f uliftFunctor.{w}) := by
  constructor
  · constructor
    intro X x y h
    have hh : f.app X x.down = f.app X y.down := congrArg ULift.down h
    apply J.superset_covering _ (Presheaf.equalizerSieve_mem J f x.down y.down hh)
    intro Y g hg
    exact congrArg ULift.up hg
  · constructor
    intro X x
    apply J.superset_covering _ (Presheaf.imageSieve_mem J f x.down)
    rintro Y g ⟨y, hy⟩
    exact ⟨ULift.up y, congrArg ULift.up hy⟩

private lemma locallyBijective_hom_bijective {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type v} (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f]
    (Z : Cᵒᵖ ⥤ Type v) (hZ : Presheaf.IsSheaf J Z) :
    Function.Bijective (fun g : Q ⟶ Z => f ≫ g) := by
  have hZ' := (isSheaf_iff_isSheaf_of_type J Z).mp hZ
  have hinj : Function.Injective (fun g : Q ⟶ Z => f ≫ g) := by
    intro g h hgh
    ext X x
    apply (hZ'.isSeparated _ (Presheaf.imageSieve_mem J f x)).ext
    intro Y k hk
    obtain ⟨p, hp⟩ := hk
    change Z.map k.op (g.app X x) = Z.map k.op (h.app X x)
    rw [← NatTrans.naturality_apply g, ← NatTrans.naturality_apply h, ← hp]
    exact congrArg (fun t : P ⟶ Z => t.app _ p) hgh
  refine ⟨hinj, ?_⟩
  intro g
  have heq : ∀ {X : Cᵒᵖ} (x y : P.obj X), f.app X x = f.app X y →
      g.app X x = g.app X y := by
    intro X x y h
    apply (hZ'.isSeparated _ (Presheaf.equalizerSieve_mem J f x y h)).ext
    intro Y k hk
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hk]
  have hex (X : Cᵒᵖ) (x : Q.obj X) : ∃ z : Z.obj X,
      ∀ (Y : C) (k : Y ⟶ X.unop) (p : P.obj (Opposite.op Y)),
        f.app _ p = Q.map k.op x → Z.map k.op z = g.app _ p := by
    let R := Presheaf.imageSieve f x
    let t : Presieve.FamilyOfElements Z R.arrows := fun Y k hk =>
      g.app _ (Presheaf.localPreimage f x k hk)
    have ht : t.Compatible := by
      intro Y₁ Y₂ W k₁ k₂ f₁ f₂ hf₁ hf₂ h
      dsimp [t]
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      apply heq
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
        Presheaf.app_localPreimage, Presheaf.app_localPreimage,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
        ← op_comp, h]
    let H := hZ' R (Presheaf.imageSieve_mem J f x)
    refine ⟨H.amalgamate t ht, ?_⟩
    intro Y k p hp
    have hk : R k := ⟨p, hp⟩
    rw [H.valid_glue ht k hk]
    apply heq
    exact (Presheaf.app_localPreimage f x k hk).trans hp.symm
  let d (X : Cᵒᵖ) (x : Q.obj X) := (hex X x).choose
  have hd (X : Cᵒᵖ) (x : Q.obj X) := (hex X x).choose_spec
  have hd_unique (X : Cᵒᵖ) (x : Q.obj X) (z : Z.obj X)
      (hz : ∀ (Y : C) (k : Y ⟶ X.unop) (p : P.obj (Opposite.op Y)),
        f.app _ p = Q.map k.op x → Z.map k.op z = g.app _ p) : z = d X x := by
    apply (hZ'.isSeparated _ (Presheaf.imageSieve_mem J f x)).ext
    rintro Y k ⟨p, hp⟩
    exact (hz Y k p hp).trans (hd X x Y k p hp).symm
  let g' : Q ⟶ Z :=
    { app := fun X => ↾(d X)
      naturality := by
        intro X Y k
        ext x
        apply (hd_unique Y (Q.map k x) (Z.map k (d X x)) ?_).symm
        intro W l p hp
        rw [← Functor.map_comp_apply]
        apply hd X x W (l ≫ k.unop) p
        simpa only [op_comp, Quiver.Hom.op_unop, Functor.map_comp,
          types_comp_apply] using hp }
  refine ⟨g', ?_⟩
  ext X p
  simpa [g', d] using hd X (f.app X p) X.unop (𝟙 _) p (by simp)

/- Plain reindexing of the sections of a type-valued functor along a functor. Unrelated to
`AlgebraicGeometry.Space.restrictSections`, which shares this short name but is the ring
homomorphism restricting a natural family of global sections of the relative affine line along
a containment of subfunctors. -/
private def restrictSections {C : Type u} [Category C] {D : Type v} [Category D]
    (F : C ⥤ D) (G : D ⥤ Type w) (s : G.sections) : (F ⋙ G).sections where
  val X := s.val (F.obj X)
  property f := s.property (F.map f)

private lemma sections_bijective_of_terminal {C D : Type u}
    [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K]
    [PreservesLimit (Functor.empty.{0} (Sheaf J (Type u)))
      (F.sheafPullback (Type u) J K)]
    (G : Dᵒᵖ ⥤ Type w) (hG : Presheaf.IsSheaf K G) :
    Function.Bijective (restrictSections F.op G) := by
  let T := (Functor.const Cᵒᵖ).obj PUnit.{u + 1}
  let P := F.op.lan.obj T
  let Q := (Functor.const Dᵒᵖ).obj PUnit.{u + 1}
  let q : P ⟶ Q := (Functor.isTerminalConst _ Types.isTerminalPUnit).from P
  have ht : IsTerminal ((presheafToSheaf K (Type u)).obj P) :=
    ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj
      (F.sheafPullback (Type u) J K) _).ofIso
        ((Functor.sheafPullbackConstruction.sheafPullbackIso F (Type u) J K).app
          (Sheaf.terminal J Types.isTerminalPUnit))
  have hq : K.W q := by
    rw [K.W_iff]
    have htQ := (Functor.isTerminalConst Dᵒᵖ Types.isTerminalPUnit).isTerminalObj
      (presheafToSheaf K (Type u)) _
    exact ⟨⟨ht.from _, ht.hom_ext _ _, htQ.hom_ext _ _⟩⟩
  have := hq.isLocallyInjective
  have := hq.isLocallySurjective
  obtain ⟨hi, hs⟩ := locallyBijective_ulift.{u, u, w} K q
  let q' := Functor.whiskerRight q uliftFunctor.{w}
  let G' := G ⋙ uliftFunctor.{u}
  have hG' : Presheaf.IsSheaf K G' :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ hG
  let η := Functor.whiskerRight (F.op.lanUnit.app T) uliftFunctor.{w} ≫
    (Functor.associator _ _ _).hom
  have : (P ⋙ uliftFunctor.{w}).IsLeftKanExtension η := inferInstance
  let e := (G'.sectionsEquivHom (ULift.{w} PUnit.{u+1})).trans
    ((Equiv.ofBijective (fun f => q' ≫ f)
      (locallyBijective_hom_bijective K q' G' hG')).trans
      ((Functor.homEquivOfIsLeftKanExtension _ η G').trans
        ((F.op ⋙ G').sectionsEquivHom (ULift.{w} PUnit.{u+1})).symm))
  have he : ∀ s, e s = restrictSections F.op G' s := by
    intro s
    apply Subtype.ext
    funext X
    rfl
  have hb : Function.Bijective (restrictSections F.op G') := by
    convert e.bijective using 1
    funext s
    exact (he s).symm
  let a := Types.sectionsEquiv.{u, w} G
  let b := Types.sectionsEquiv.{u, w} (F.op ⋙ G)
  rw [show restrictSections F.op G = b.symm ∘ restrictSections F.op G' ∘ a from rfl]
  exact b.symm.bijective.comp (hb.comp a.bijective)


section

open CategoryTheory.Pseudofunctor

private def componentSectionInl (C : SimplicialSite.{u})
    (G : Sheaf C.totalTopology (Type w))
    {n m : SimplexCategory} (α : n ⟶ m)
    (s : ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).op ⋙ G.obj).sections) :
    ((C.underlying.map α).toFunctor.op ⋙
      (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op m)).op ⋙ G.obj).sections :=
  { val U := G.obj.map ((continuousInclusionTransition C α).app U.unop).op (s.val U)
    property := by
      intro U V f
      change G.obj.map _ (G.obj.map _ _) = G.obj.map _ _
      rw [← Functor.map_comp_apply]
      have h := s.property f
      change G.obj.map ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).map f.unop).op
        (s.val U) = s.val V at h
      rw [← h, ← Functor.map_comp_apply]
      apply congrArg (fun k => G.obj.map k (s.val U))
      exact congrArg Quiver.Hom.op ((continuousInclusionTransition C α).naturality f.unop) }

private lemma inl_restrictSections_bijective (C : SimplicialSite.{u})
    {n m : SimplexCategory} (α : n ⟶ m)
    (G : Sheaf ((C.coverage m).toGrothendieck) (Type w)) :
    Function.Bijective (restrictSections (C.underlying.map α).toFunctor.op G.obj) := by
  have := (C.isMorphismOfSites α).isContinuous
  have := (C.isMorphismOfSites α).preservesFiniteLimits
  exact sections_bijective_of_terminal _ ((C.coverage n).toGrothendieck)
    ((C.coverage m).toGrothendieck) G.obj G.property

private def extendComponentSectionInl (C : SimplicialSite.{u})
    (G : Sheaf C.totalTopology (Type w))
    {n m : SimplexCategory} (α : n ⟶ m)
    (s : ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).op ⋙ G.obj).sections) :
    ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op m)).op ⋙ G.obj).sections :=
  (Equiv.ofBijective _ (inl_restrictSections_bijective C α
    ((restrict ⟨Sum.inl C⟩ m).obj G))).symm (componentSectionInl C G α s)

private lemma extendComponentSectionInl_spec (C : SimplicialSite.{u})
    (G : Sheaf C.totalTopology (Type w))
    {n m : SimplexCategory} (α : n ⟶ m)
    (s : ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).op ⋙ G.obj).sections)
    (U : (C.underlying.obj n)ᵒᵖ) :
    (extendComponentSectionInl C G α s).val ((C.underlying.map α).toFunctor.op.obj U) =
      G.obj.map ((continuousInclusionTransition C α).app U.unop).op (s.val U) :=
  congrArg (fun x => x.val U)
    ((Equiv.ofBijective _ (inl_restrictSections_bijective C α
      ((restrict ⟨Sum.inl C⟩ m).obj G))).apply_symm_apply (componentSectionInl C G α s))

/-- The Cartesian lift of a composite simplex map, after the transport comparing the two
images of an object, is the composite of the two Cartesian lifts. -/
private lemma continuousInclusionTransition_comp_eqToHom (C : SimplicialSite.{u})
    {n m l : SimplexCategory} (α : n ⟶ m) (β : m ⟶ l) (V : C.underlying.obj n)
    (h : (C.underlying.map β).toFunctor.obj ((C.underlying.map α).toFunctor.obj V) =
      (C.underlying.map (α ≫ β)).toFunctor.obj V) :
    (continuousInclusionTransition C β).app ((C.underlying.map α).toFunctor.obj V) ≫
        (continuousInclusionTransition C α).app V =
      (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op l)).map (eqToHom h) ≫
        (continuousInclusionTransition C (α ≫ β)).app V := by
  rw [continuousInclusionTransition_comp C α β V, ← Category.assoc,
    ← (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op l)).map_comp]
  simp

/-- The Cartesian lift of an identity simplex map is the fibre inclusion of the transport
comparing the two images of an object. -/
private lemma continuousInclusionTransition_id_eqToHom (C : SimplicialSite.{u})
    (n : SimplexCategory) (V : C.underlying.obj n)
    (h : (C.underlying.map (𝟙 n)).toFunctor.obj V = V) :
    (continuousInclusionTransition C (𝟙 n)).app V =
      (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).map (eqToHom h) := by
  rw [continuousInclusionTransition_id C n V]
  exact congrArg (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).map (by simp)

private lemma extendComponentSectionInl_comp (C : SimplicialSite.{u})
    (G : Sheaf C.totalTopology (Type w))
    {n m l : SimplexCategory} (α : n ⟶ m) (β : m ⟶ l)
    (s : ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).op ⋙ G.obj).sections) :
    componentSectionInl C G β (extendComponentSectionInl C G α s) =
      restrictSections (C.underlying.map β).toFunctor.op _
        (extendComponentSectionInl C G (α ≫ β) s) := by
  have := (C.isMorphismOfSites β).isContinuous
  let H : Sheaf ((C.coverage m).toGrothendieck) (Type w) :=
    ((C.underlying.map β).toFunctor.sheafPushforwardContinuous (Type w)
      ((C.coverage m).toGrothendieck) ((C.coverage l).toGrothendieck)).obj
      ((restrict ⟨Sum.inl C⟩ l).obj G)
  apply (inl_restrictSections_bijective C α H).injective
  apply Subtype.ext
  funext U
  change G.obj.map ((continuousInclusionTransition C β).app
      ((C.underlying.map α).toFunctor.obj U.unop)).op
      ((extendComponentSectionInl C G α s).val ((C.underlying.map α).toFunctor.op.obj U)) =
    (extendComponentSectionInl C G (α ≫ β) s).val
      (Opposite.op ((C.underlying.map β).toFunctor.obj
        ((C.underlying.map α).toFunctor.obj U.unop)))
  rw [extendComponentSectionInl_spec]
  let e : (C.underlying.map β).toFunctor.obj ((C.underlying.map α).toFunctor.obj U.unop) ⟶
      (C.underlying.map (α ≫ β)).toFunctor.obj U.unop := eqToHom (by
        rw [C.underlying.map_comp]; rfl)
  have hp := (extendComponentSectionInl C G (α ≫ β) s).property e.op
  change G.obj.map ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op l)).map e).op
    ((extendComponentSectionInl C G (α ≫ β) s).val
      ((C.underlying.map (α ≫ β)).toFunctor.op.obj U)) = _ at hp
  rw [extendComponentSectionInl_spec] at hp
  rw [← hp, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact congrArg (fun k => G.obj.map k (s.val U)) (congrArg Quiver.Hom.op
    (continuousInclusionTransition_comp_eqToHom C α β U.unop _))

private lemma extendComponentSectionInl_id (C : SimplicialSite.{u})
    (G : Sheaf C.totalTopology (Type w)) (n : SimplexCategory)
    (s : ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).op ⋙ G.obj).sections) :
    extendComponentSectionInl C G (𝟙 n) s = s := by
  apply (inl_restrictSections_bijective C (𝟙 n) ((restrict ⟨Sum.inl C⟩ n).obj G)).injective
  apply Subtype.ext
  funext U
  change (extendComponentSectionInl C G (𝟙 n) s).val
      ((C.underlying.map (𝟙 n)).toFunctor.op.obj U) =
    s.val (Opposite.op ((C.underlying.map (𝟙 n)).toFunctor.obj U.unop))
  rw [extendComponentSectionInl_spec]
  let e : (C.underlying.map (𝟙 n)).toFunctor.obj U.unop ⟶ U.unop :=
    eqToHom (by rw [C.underlying.map_id]; rfl)
  have hp := s.property e.op
  change G.obj.map ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).map e).op
    (s.val U) = _ at hp
  rw [← hp]
  exact congrArg (fun k => G.obj.map k (s.val U)) (congrArg Quiver.Hom.op
    (continuousInclusionTransition_id_eqToHom C n U.unop _))


private def componentSimplexSection (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (α : n ⟶ m) :
    ((componentFunctor S m).op ⋙ simplexIndices.{u, w} S n).sections where
  val U := by rcases S with ⟨C | C⟩ <;> exact ULift.up α
  property := by
    intro U V k
    rcases S with ⟨C | C⟩ <;>
      change ULift.up (α ≫ 𝟙 m) = ULift.up α
    all_goals rw [Category.comp_id]

private def simplexHomComponentSection (S : SimplicialSiteSituation.{u})
    (G : S.totalCategoryᵒᵖ ⥤ Type w) {n m : SimplexCategory}
    (f : simplexIndices S n ⟶ G) (α : n ⟶ m) :
    ((componentFunctor S m).op ⋙ G).sections where
  val U := f.app ((componentFunctor S m).op.obj U) ((componentSimplexSection S α).val U)
  property := by
    intro U V k
    exact (NatTrans.naturality_apply f ((componentFunctor S m).op.map k)
      ((componentSimplexSection S α).val U)).symm.trans
        (congrArg (fun x => f.app ((componentFunctor S m).op.obj V) x)
          ((componentSimplexSection S α).property k))

private lemma coGrothendieck_factor (C : SimplicialSite.{u})
    {X Y : CoGrothendieck C.totalPseudofunctor} (f : X ⟶ Y) :
    (CoGrothendieck.ι C.totalPseudofunctor X.base).map f.fiber ≫
      (continuousInclusionTransition C f.base.unop).app Y.fiber = f :=
  CoGrothendieck.ι_map_comp_ιNatTrans_app C.totalPseudofunctor f.base f.fiber

private def simplexHomOfSectionInl (C : SimplicialSite.{u})
    (G : Sheaf C.totalTopology (Type w)) (n : SimplexCategory)
    (s : ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).op ⋙ G.obj).sections) :
    simplexIndices ⟨Sum.inl C⟩ n ⟶ G.obj where
  app X := ↾fun a => (extendComponentSectionInl C G a.down s).val (Opposite.op X.unop.fiber)
  naturality := by
    intro X Y k
    ext a
    change (extendComponentSectionInl C G (a.down ≫ k.unop.base.unop) s).val
        (Opposite.op Y.unop.fiber) =
      G.obj.map k ((extendComponentSectionInl C G a.down s).val (Opposite.op X.unop.fiber))
    have hc := congrArg (fun t => t.val (Opposite.op X.unop.fiber))
      (extendComponentSectionInl_comp C G a.down k.unop.base.unop s)
    have hp := (extendComponentSectionInl C G (a.down ≫ k.unop.base.unop) s).property
      k.unop.fiber.op
    change G.obj.map ((CoGrothendieck.ι C.totalPseudofunctor Y.unop.base).map
        k.unop.fiber).op
      ((extendComponentSectionInl C G (a.down ≫ k.unop.base.unop) s).val
        (Opposite.op ((C.underlying.map k.unop.base.unop).toFunctor.obj
          X.unop.fiber))) = _ at hp
    dsimp [componentSectionInl, restrictSections] at hc
    refine hp.symm.trans ?_
    refine (congrArg (fun t => G.obj.map ((CoGrothendieck.ι C.totalPseudofunctor
      Y.unop.base).map k.unop.fiber).op t) hc.symm).trans ?_
    refine (Functor.map_comp_apply G.obj _ _ _).symm.trans ?_
    exact congrArg (fun g => G.obj.map g ((extendComponentSectionInl C G a.down s).val
      (Opposite.op X.unop.fiber))) (congrArg Quiver.Hom.op (coGrothendieck_factor C k.unop))

private lemma simplexHomComponentSection_eq_extend (C : SimplicialSite.{u})
    (G : Sheaf C.totalTopology (Type w)) {n m : SimplexCategory}
    (f : simplexIndices ⟨Sum.inl C⟩ n ⟶ G.obj) (α : n ⟶ m) :
    simplexHomComponentSection ⟨Sum.inl C⟩ G.obj f α =
      extendComponentSectionInl C G α
        (simplexHomComponentSection ⟨Sum.inl C⟩ G.obj f (𝟙 n)) := by
  apply (inl_restrictSections_bijective C α ((restrict ⟨Sum.inl C⟩ m).obj G)).injective
  apply Subtype.ext
  funext U
  change f.app ((componentFunctor ⟨Sum.inl C⟩ m).op.obj
    ((C.underlying.map α).toFunctor.op.obj U)) (ULift.up α) =
    (extendComponentSectionInl C G α _).val ((C.underlying.map α).toFunctor.op.obj U)
  rw [extendComponentSectionInl_spec]
  change f.app ((componentFunctor ⟨Sum.inl C⟩ m).op.obj
    ((C.underlying.map α).toFunctor.op.obj U)) (ULift.up α) =
      G.obj.map ((continuousInclusionTransition C α).app U.unop).op
        (f.app _ (ULift.up (𝟙 n)))
  refine Eq.trans ?_ (NatTrans.naturality_apply f _ _)
  congr 1
  exact congrArg ULift.up (Category.id_comp α).symm

private lemma simplexHomSection_bijective_inl (C : SimplicialSite.{u})
    (G : Sheaf C.totalTopology (Type w)) (n : SimplexCategory) :
    Function.Bijective (fun f : simplexIndices ⟨Sum.inl C⟩ n ⟶ G.obj =>
      simplexHomComponentSection ⟨Sum.inl C⟩ G.obj f (𝟙 n)) := by
  constructor
  · intro f g h
    ext X a
    have hf := congrArg (fun s => s.val (Opposite.op X.unop.fiber))
      (simplexHomComponentSection_eq_extend C G f a.down)
    have hg := congrArg (fun s => s.val (Opposite.op X.unop.fiber))
      (simplexHomComponentSection_eq_extend C G g a.down)
    exact hf.trans ((congrArg (fun s => (extendComponentSectionInl C G a.down s).val
      (Opposite.op X.unop.fiber)) h).trans hg.symm)
  · intro s
    refine ⟨simplexHomOfSectionInl C G n s, ?_⟩
    apply Subtype.ext
    funext U
    exact congrArg (fun t => t.val U) (extendComponentSectionInl_id C G n s)

private lemma grothendieck_factor (C : CocontinuousSimplicialSite.{u})
    {X Y : CategoryTheory.Grothendieck C.underlying} (f : X ⟶ Y) :
    (⟨f.base, 𝟙 _⟩ : X ⟶
      (CategoryTheory.Grothendieck.ι C.underlying Y.base).obj
        ((C.underlying.map f.base).toFunctor.obj X.fiber)) ≫
      (CategoryTheory.Grothendieck.ι C.underlying Y.base).map f.fiber = f :=
  CategoryTheory.Grothendieck.ιNatTrans_app_comp_ι_map f.base f.fiber

private def simplexHomOfSectionInr (C : CocontinuousSimplicialSite.{u})
    (G : (CategoryTheory.Grothendieck C.underlying)ᵒᵖ ⥤ Type w) (n : SimplexCategory)
    (s : ((CategoryTheory.Grothendieck.ι C.underlying (Opposite.op n)).op ⋙ G).sections) :
    simplexIndices ⟨Sum.inr C⟩ n ⟶ G where
  app X := ↾fun a =>
    G.map (Quiver.Hom.op (⟨a.down.op, 𝟙 _⟩ : X.unop ⟶
      (CategoryTheory.Grothendieck.ι C.underlying (Opposite.op n)).obj
        ((C.underlying.map a.down.op).toFunctor.obj X.unop.fiber)))
      (s.val (Opposite.op ((C.underlying.map a.down.op).toFunctor.obj X.unop.fiber)))
  naturality := by
    intro X Y k
    ext a
    let c : X.unop ⟶ (CategoryTheory.Grothendieck.ι C.underlying (Opposite.op n)).obj
        ((C.underlying.map a.down.op).toFunctor.obj X.unop.fiber) := ⟨a.down.op, 𝟙 _⟩
    let h := k.unop ≫ c
    have hp := s.property h.fiber.op
    change G.map (Quiver.Hom.op (⟨h.base, 𝟙 _⟩ : Y.unop ⟶
      (CategoryTheory.Grothendieck.ι C.underlying (Opposite.op n)).obj
        ((C.underlying.map h.base).toFunctor.obj Y.unop.fiber)))
      (s.val (Opposite.op ((C.underlying.map h.base).toFunctor.obj Y.unop.fiber))) =
      G.map k (G.map c.op (s.val _))
    change G.map ((CategoryTheory.Grothendieck.ι C.underlying (Opposite.op n)).map
      h.fiber).op (s.val _) = _ at hp
    rw [← hp, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
    apply congrArg (fun f => G.map f _)
    exact congrArg Quiver.Hom.op (grothendieck_factor C h)

private lemma simplexHomSection_bijective_inr (C : CocontinuousSimplicialSite.{u})
    (G : (CategoryTheory.Grothendieck C.underlying)ᵒᵖ ⥤ Type w) (n : SimplexCategory) :
    Function.Bijective (fun f : simplexIndices ⟨Sum.inr C⟩ n ⟶ G =>
      simplexHomComponentSection ⟨Sum.inr C⟩ G f (𝟙 n)) := by
  have heval (f : simplexIndices ⟨Sum.inr C⟩ n ⟶ G) (X) (a) :
      f.app X a = (simplexHomOfSectionInr C G n
        (simplexHomComponentSection ⟨Sum.inr C⟩ G f (𝟙 n))).app X a := by
    let c : X.unop ⟶ (CategoryTheory.Grothendieck.ι C.underlying (Opposite.op n)).obj
        ((C.underlying.map a.down.op).toFunctor.obj X.unop.fiber) := ⟨a.down.op, 𝟙 _⟩
    change f.app X a = G.map c.op (f.app _ (ULift.up (𝟙 n)))
    refine Eq.trans ?_ (NatTrans.naturality_apply f _ _)
    congr 1
    apply ULift.ext
    exact (Category.id_comp a.down).symm
  constructor
  · intro f g h
    ext X a
    change f.app X a = g.app X a
    exact (heval f X a).trans
      ((congrArg (fun s => (simplexHomOfSectionInr C G n s).app X a) h).trans
        (heval g X a).symm)
  · intro s
    refine ⟨simplexHomOfSectionInr C G n s, ?_⟩
    apply Subtype.ext
    funext U
    let e : U.unop ⟶ (C.underlying.map (𝟙 (Opposite.op n))).toFunctor.obj U.unop :=
      eqToHom (by rw [C.underlying.map_id]; rfl)
    have hp := s.property e.op
    change G.map (Quiver.Hom.op (⟨(𝟙 n).op, 𝟙 _⟩ :
        (CategoryTheory.Grothendieck.ι C.underlying (Opposite.op n)).obj U.unop ⟶
        (CategoryTheory.Grothendieck.ι C.underlying (Opposite.op n)).obj
          ((C.underlying.map (𝟙 n).op).toFunctor.obj U.unop))) (s.val _) = s.val U
    change G.map ((CategoryTheory.Grothendieck.ι C.underlying (Opposite.op n)).map e).op
      (s.val _) = s.val U at hp
    rw [← hp]
    apply congrArg (fun k => G.map k _)
    apply congrArg Quiver.Hom.op
    apply CategoryTheory.Grothendieck.ext _ _ (by simp [CategoryTheory.Grothendieck.ι])
    simp [CategoryTheory.Grothendieck.ι, e]

private lemma simplexHomSection_bijective (S : SimplicialSiteSituation.{u})
    (G : Sheaf S.totalTopology (Type w)) (n : SimplexCategory) :
    Function.Bijective (fun f : simplexIndices S n ⟶ G.obj =>
      simplexHomComponentSection S G.obj f (𝟙 n)) := by
  rcases S with ⟨C | C⟩
  · exact simplexHomSection_bijective_inl C G n
  · exact simplexHomSection_bijective_inr C G.obj n

end


open CategoryTheory.Limits
open scoped ZeroObject

private lemma epi_map_kernelLift_of_exact
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Abelian D]
    [HasFiniteLimits C] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (S : ShortComplex C) (h : (S.map F).Exact) :
    Epi (F.map (kernel.lift S.g S.f S.zero)) := by
  let k := (KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g)).map F
  let hk := KernelFork.mapIsLimit _ (kernelIsKernel S.g) F
  let l := h.leftHomologyDataOfIsLimitKernelFork k hk
  have : Epi l.f' := h.epi_f' l
  have hl : l.f' = F.map (kernel.lift S.g S.f S.zero) := by
    apply Fork.IsLimit.hom_ext hk
    change l.f' ≫ l.i = F.map (kernel.lift S.g S.f S.zero) ≫ F.map (kernel.ι S.g)
    rw [l.f'_i, ← F.map_comp, kernel.lift_ι]
    rfl
  rwa [hl] at this

private lemma exact_of_map
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Abelian D]
    [HasFiniteLimits C] [HasZeroObject C] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] (S : ShortComplex C) [HasCokernel S.f]
    [PreservesColimit (parallelPair S.f 0) F] (h : (S.map F).Exact) : S.Exact := by
  let r := ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel S
  have hr : r.IsPreservedBy F := ⟨inferInstance, inferInstance⟩
  have hz : IsZero r.H := by
    apply IsZero.of_full_of_faithful_of_isZero F
    exact ((r.map F).exact_iff).1 h
  have he : Epi (kernel.lift S.g S.f S.zero) :=
    F.epi_of_epi_map (epi_map_kernelLift_of_exact F S h)
  let l : S.LeftHomologyData :=
    { K := kernel S.g
      H := 0
      i := kernel.ι S.g
      π := 0
      wi := kernel.condition S.g
      hi := kernelIsKernel S.g
      wπ := comp_zero
      hπ := CokernelCofork.IsColimit.ofEpiOfIsZero _ he (isZero_zero C) }
  have : IsIso (ShortComplex.leftRightHomologyComparison' l r) :=
    (isZero_zero C).isIso hz _
  exact ⟨⟨ShortComplex.HomologyData.ofIsIsoLeftRightHomologyComparison' l r,
    isZero_zero C⟩⟩

private lemma exact_of_map_of_exact_next
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Abelian D]
    [HasFiniteLimits C] [HasZeroObject C] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] (S : ShortComplex C) {Y : C} (t : S.X₃ ⟶ Y)
    (ht : S.g ≫ t = 0) (h : (S.map F).Exact)
    (hnext : ((ShortComplex.mk S.g t ht).map F).Exact) : S.Exact := by
  let p := kernel.lift t S.g ht
  have hp : S.f ≫ p = 0 := by
    rw [← cancel_mono (kernel.ι t), Category.assoc, kernel.lift_ι,
      Limits.zero_comp, S.zero]
  let T := ShortComplex.mk S.f p hp
  let φ : T ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι t
      comm₁₂ := by simp [T]
      comm₂₃ := by simp [T, p] }
  have : Epi (F.mapShortComplex.map φ).τ₁ := by
    change Epi (F.map (𝟙 S.X₁))
    rw [F.map_id]
    infer_instance
  have : IsIso (F.mapShortComplex.map φ).τ₂ := by
    change IsIso (F.map (𝟙 S.X₂))
    rw [F.map_id]
    infer_instance
  have : Mono (F.mapShortComplex.map φ).τ₃ := by
    change Mono (F.map (kernel.ι t))
    infer_instance
  have hm : (T.map F).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (F.mapShortComplex.map φ)).2 h
  have ep : Epi (F.map p) := epi_map_kernelLift_of_exact F (ShortComplex.mk S.g t ht) hnext
  have : Epi (T.map F).g := ep
  have hc : IsColimit ((CokernelCofork.ofπ p hp).map F) := hm.gIsCokernel
  have hc' := (CokernelCofork.isColimitMapCoconeEquiv _ F).symm hc
  have hC := isColimitOfReflects F hc'
  let : HasCokernel S.f := ⟨⟨_, hC⟩⟩
  let : PreservesColimit (parallelPair S.f 0) F :=
    preservesColimit_of_preserves_colimit_cocone hC hc'
  exact exact_of_map F S h

private lemma presheaf_exact_of_evaluation
    {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (S : ShortComplex (PresheafOfModules.{w} R))
    (h : ∀ U, (S.map (PresheafOfModules.evaluation R U)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  ext1 U
  have hz : IsZero ((PresheafOfModules.evaluation R U).obj S.homology) :=
    IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).1 (h U))
      (S.mapHomologyIso (PresheafOfModules.evaluation R U)).symm
  exact hz.eq_of_src _ _

private lemma isSheafFor_map_of_comp
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type*) {X : C} (R : Presieve X)
    (h : Presieve.IsSheafFor (F.op ⋙ P) R) :
    Presieve.IsSheafFor P (R.map F) := by
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.map_ofArrows, Presieve.isSheafFor_arrows_iff]
  rw [Presieve.isSheafFor_arrows_iff] at h
  intro x hx
  apply h x
  intro i j Z a b hab
  exact hx i j (F.obj Z) (F.map a) (F.map b) (by simpa only [← F.map_comp] using congrArg F.map hab)

private lemma isSheaf_of_componentwise (S : SimplicialSiteSituation.{u})
    (P : S.totalCategoryᵒᵖ ⥤ Type w)
    (h : ∀ n, Presieve.IsSheaf (S.componentTopology n)
      ((componentFunctor S n).op ⋙ P)) :
    Presieve.IsSheaf S.totalTopology P := by
  rcases S with ⟨C | C⟩
  · have := C.totalCoverage_hasPullbacks
    have := C.totalCoverage_isStableUnderBaseChange
    rw [show SimplicialSiteSituation.totalTopology ⟨Sum.inl C⟩ =
        C.totalCoverage.toGrothendieck from rfl,
      Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
    rintro X R ⟨T, hT, rfl⟩
    exact isSheafFor_map_of_comp _ P T
      ((h X.base.unop).isSheafFor_of_mem_precoverage hT)
  · let K := coverageFromIsSite (SimplicialCoverings.total C.underlying C.coverage)
      (CategoryTheory.SimplicialCoverings.total_isSite C.underlying C.coverage C.isSite
        C.isCocontinuous C.hasCoverPullbacks)
    change Presieve.IsSheaf K.toPrecoverage.toGrothendieck P
    rw [Coverage.toGrothendieck_toPrecoverage, Presieve.isSheaf_coverage]
    rintro X R ⟨E, hE, rfl⟩
    obtain ⟨T, hT, hE⟩ := hE
    change E = T.map (Grothendieck.ι C.underlying X.base) at hE
    rw [hE, PreZeroHypercover.presieve₀_map]
    exact isSheafFor_map_of_comp _ P T.presieve₀
      ((h X.base.unop).isSheafFor_of_mem_precoverage ⟨T, hT, rfl⟩)

private noncomputable def freeConstUnderlyingIso
    {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ RingCat.{u})
    (I : Type u) [Finite I] :
    (PresheafOfModules.freeObj (R := R) ((Functor.const Cᵒᵖ).obj I)).presheaf ⋙
        forget AddCommGrpCat.{u} ≅
      (R ⋙ forget RingCat.{u}) ⋙ coyoneda.obj (Opposite.op I) := by
  classical
  letI := Fintype.ofFinite I
  refine NatIso.ofComponents
    (fun U => ((Finsupp.equivFunOnFinite :
      (I →₀ R.obj U) ≃ (I → R.obj U)).trans TypeCat.homEquiv.symm).toIso) ?_
  intro U V f
  dsimp [PresheafOfModules.presheaf, PresheafOfModules.freeObj, ModuleCat.free,
    ModuleCat.restrictScalars]
  ext x i
  change Finsupp.toFun (α := I) (M := R.obj V) ((ModuleCat.freeDesc (R := R.obj U)
    (M := (ModuleCat.restrictScalars (R.map f).hom).obj
      ((ModuleCat.free (R.obj V)).obj I)) (↾fun j => ModuleCat.freeMk j) x : I →₀ R.obj V)) i =
    (R.map f).hom (x i)
  induction x using Finsupp.induction with
  | zero =>
    change (0 : R.obj V) = (R.map f).hom 0
    exact (map_zero _).symm
  | single_add j r x hj hr hx =>
    simp only [map_add]
    rw [show ∀ a b : I →₀ R.obj V, (a + b).toFun i = a.toFun i + b.toFun i
      from fun a b => Finsupp.add_apply a b i, Finsupp.add_apply, map_add]
    change (Finsupp.toFun (α := I) (M := R.obj V) _ i) +
      (Finsupp.toFun (α := I) (M := R.obj V) _ i) =
      (R.map f).hom ((Finsupp.single j r) i) + (R.map f).hom (x i)
    refine congrArg₂ (fun a b : R.obj V => a + b) ?_ hx
    have hsingle : Finsupp.single j r = r • ModuleCat.freeMk (R := R.obj U) j := by
      apply Finsupp.ext
      intro k
      change (Finsupp.single j r) k = r * (Finsupp.single j (1 : R.obj U)) k
      by_cases h : j = k <;> simp [h]
    rw [hsingle, map_smul]
    simp only [ModuleCat.freeDesc_apply]
    change ((R.map f).hom r • Finsupp.single j (1 : R.obj V)) i =
      (R.map f).hom ((r • Finsupp.single j (1 : R.obj U)) i)
    by_cases h : j = i <;> simp [h]

private lemma freeConst_isSheaf
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (I : Type u) [Finite I] :
    Presheaf.IsSheaf J
      (PresheafOfModules.freeObj (R := R.obj) ((Functor.const Cᵒᵖ).obj I)).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{u})
  apply (Presheaf.isSheaf_of_iso_iff (freeConstUnderlyingIso R.obj I)).2
  exact Presheaf.isSheaf_comp_of_isSheaf _ _ _
    (Presheaf.isSheaf_comp_of_isSheaf _ (SheafOfModules.unit R).val.presheaf
      (forget AddCommGrpCat.{u}) (SheafOfModules.unit R).isSheaf)

private noncomputable def componentFreeRestrictionIso
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (n m : SimplexCategory) :
    (componentFunctor S m).op ⋙ (componentFreePresheaf S O n).presheaf ≅
      (PresheafOfModules.freeObj
        (R := (componentFunctor S m).op ⋙ O.obj)
        ((Functor.const (S.component m)ᵒᵖ).obj (ULift.{u} (n ⟶ m)))).presheaf := by
  rcases S with ⟨C | C⟩ <;>
    refine NatIso.ofComponents (fun U => Iso.refl _) ?_
  all_goals
    intro U V f
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    dsimp [componentFunctor, componentFreePresheaf, PresheafOfModules.presheaf,
      PresheafOfModules.freeObj, simplexIndices, totalSimplexDegree]
    congr 4
    apply congrArg ModuleCat.freeDesc
    apply ConcreteCategory.hom_ext
    intro x
    apply congrArg ModuleCat.freeMk
    change ULift.up (x.down ≫ 𝟙 m) = x
    apply ULift.ext
    exact Category.comp_id _

private lemma componentFreePresheaf_isSheaf
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (n : SimplexCategory) :
    Presheaf.IsSheaf S.totalTopology (componentFreePresheaf S O n).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u})
  rw [isSheaf_iff_isSheaf_of_type]
  apply isSheaf_of_componentwise
  intro m
  rw [← isSheaf_iff_isSheaf_of_type]
  apply (Presheaf.isSheaf_of_iso_iff
    (Functor.isoWhiskerRight (componentFreeRestrictionIso S O n m)
      (forget AddCommGrpCat.{u}))).2
  exact Presheaf.isSheaf_comp_of_isSheaf _ _ _
    (freeConst_isSheaf
      (componentRingSheaf S O m)
      (ULift.{u} (n ⟶ m)))

private def componentFreeSheaf (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory) :
    SheafOfModules.{u} O where
  val := componentFreePresheaf S O n
  isSheaf := componentFreePresheaf_isSheaf S O n

private abbrev linearizedStandardSimplex (R : Type u) [Ring R] (m : SimplexCategory) :
    SimplicialObject.Augmented (ModuleCat.{u} R) :=
  ((SimplicialObject.Augmented.whiskering (Type u) (ModuleCat.{u} R)).obj
    (ModuleCat.free R)).obj (SSet.Augmented.stdSimplex.obj m)

/-- The canonical map between the component free modules induced by a simplex
map. It sends the generator labelled `α` to the generator labelled `φ ≫ α`. -/
public noncomputable def componentFreeMap (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    componentFreePresheaf S O n ⟶ componentFreePresheaf S O m :=
  (PresheafOfModules.free _).map (simplexIndicesMap S φ)

private def simplexIndicesSimplicial (S : SimplicialSiteSituation.{u}) :
    SimplicialObject (S.totalCategoryᵒᵖ ⥤ Type u) :=
  coyoneda ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙
    (Functor.whiskeringLeft _ _ _).obj (totalSimplexDegree S).leftOp

private def componentFreeSimplicialPresheaf (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) :
    SimplicialObject (PresheafOfModules.{u} O.obj) :=
  simplexIndicesSimplicial S ⋙ PresheafOfModules.free O.obj

private def componentFreeSimplicial (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) :
    SimplicialObject (SheafOfModules.{u} O) where
  obj n := componentFreeSheaf S O n.unop
  map φ := ⟨(componentFreeSimplicialPresheaf S O).map φ⟩
  map_id n := by
    apply (SheafOfModules.forget O).map_injective
    exact (componentFreeSimplicialPresheaf S O).map_id n
  map_comp φ ψ := by
    apply (SheafOfModules.forget O).map_injective
    exact (componentFreeSimplicialPresheaf S O).map_comp φ ψ

private def componentFreeComplex (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) :
    ChainComplex (SheafOfModules.{u} O) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (componentFreeSimplicial S O)

private lemma componentFreeComplex_d (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : ℕ) :
    ((componentFreeComplex S O).d (n + 1) n).val =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        componentFreeMap S O (SimplexCategory.δ i) := by
  change (SheafOfModules.forget O).map
    (((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (componentFreeSimplicial S O)).d (n + 1) n) = _
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  change (SheafOfModules.forget O).map
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (componentFreeSimplicial S O).δ i) = _
  simp only [Functor.map_sum, Functor.map_zsmul]
  rfl

private def componentFreeSimplicialEvaluationIso
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (U : S.totalCategoryᵒᵖ) :
    componentFreeSimplicial S O ⋙
      (SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U) ≅
      (linearizedStandardSimplex (O.obj.obj U)
        ((totalSimplexDegree S).obj U.unop).unop).left := by
  refine NatIso.ofComponents (fun n => Iso.refl _) ?_
  intro n m φ
  ext x
  rfl

private lemma componentFreeComplex_evaluation_exactAt
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (U : S.totalCategoryᵒᵖ) (n : ℕ) (hn : 0 < n) :
    (((SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U).mapHomologicalComplex
      _).obj (componentFreeComplex S O)).ExactAt n := by
  let T := linearizedStandardSimplex (O.obj.obj U) ((totalSimplexDegree S).obj U.unop).unop
  let e := (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U)).app
        (componentFreeSimplicial S O) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
      (componentFreeSimplicialEvaluationIso S O U)
  apply HomologicalComplex.ExactAt.of_iso (e := e.symm)
  let ed := (SSet.Augmented.StandardSimplex.extraDegeneracy
    ((totalSimplexDegree S).obj U.unop).unop).map (ModuleCat.free (O.obj.obj U))
  let h := ed.homotopyEquiv
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
  have hz : CategoryTheory.Limits.IsZero
      (((ChainComplex.single₀ (ModuleCat.{u} (O.obj.obj U))).obj
        (T.right)).homology n) := by
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    cases n with
    | zero => omega
    | succ k => exact ChainComplex.exactAt_succ_single_obj _ k
  exact CategoryTheory.Limits.IsZero.of_iso hz (h.toHomologyIso n)

/-- The canonical augmentation sends every simplex generator to `1`. -/
public noncomputable def componentFreeAugmentation (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory) :
    componentFreePresheaf S O n ⟶ (SheafOfModules.unit O).val :=
  PresheafOfModules.freeObjDesc (G := (SheafOfModules.unit O).val)
    { app := fun U => ↾fun _ => (1 : O.obj.obj U)
      naturality := by
        intro U V f
        ext x
        exact (O.obj.map f).hom.map_one.symm }

private lemma componentFreeMap_comp_augmentation
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    componentFreeMap S O φ ≫ componentFreeAugmentation S O m =
      componentFreeAugmentation S O n := by
  ext1 U
  change ((ModuleCat.free (O.obj.obj U)).map ((simplexIndicesMap S φ).app U)) ≫
      ModuleCat.freeDesc (M := ModuleCat.of (O.obj.obj U) (O.obj.obj U))
        (↾fun _ => (1 : O.obj.obj U)) =
    ModuleCat.freeDesc (M := ModuleCat.of (O.obj.obj U) (O.obj.obj U))
      (↾fun _ => (1 : O.obj.obj U))
  apply ModuleCat.free_hom_ext
  intro x
  rw [ModuleCat.comp_apply, ModuleCat.free_map_apply, ModuleCat.freeDesc_apply,
    ModuleCat.freeDesc_apply]
  rfl

private def componentFreeAugmented (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) :
    SimplicialObject.Augmented (SheafOfModules.{u} O) where
  left := componentFreeSimplicial S O
  right := SheafOfModules.unit O
  hom :=
    { app := fun n => ⟨componentFreeAugmentation S O n.unop⟩
      naturality := by
        intro m n φ
        apply (SheafOfModules.forget O).map_injective
        change componentFreeMap S O φ.unop ≫ componentFreeAugmentation S O n.unop =
          componentFreeAugmentation S O m.unop ≫ 𝟙 _
        rw [Category.comp_id]
        exact componentFreeMap_comp_augmentation S O φ.unop }

private lemma componentFreeComplex_augmentation_comp
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u}) :
    (componentFreeComplex S O).d 1 0 ≫
      (⟨componentFreeAugmentation S O ⦋0⦌⟩ :
        (componentFreeComplex S O).X 0 ⟶ SheafOfModules.unit O) = 0 := by
  apply (SheafOfModules.forget O).map_injective
  change ((componentFreeComplex S O).d 1 0).val ≫
    componentFreeAugmentation S O ⦋0⦌ = 0
  rw [componentFreeComplex_d]
  change (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
    componentFreeMap S O (SimplexCategory.δ i)) ≫ componentFreeAugmentation S O ⦋0⦌ = 0
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one,
    pow_one, neg_smul, Preadditive.add_comp, Preadditive.neg_comp,
    componentFreeMap_comp_augmentation, add_neg_cancel]

private def componentFreeAugmentedEvaluationIso
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (U : S.totalCategoryᵒᵖ) :
    ((SimplicialObject.Augmented.whiskering _ _).obj
      (SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U)).obj
        (componentFreeAugmented S O) ≅
    linearizedStandardSimplex (O.obj.obj U)
      ((totalSimplexDegree S).obj U.unop).unop := by
  let R := O.obj.obj U
  let e := (Finsupp.uniqueLinearEquiv R R (default : ⊤_ (Type u))).toModuleIso
  refine Comma.isoMk (componentFreeSimplicialEvaluationIso S O U) e.symm ?_
  ext n x
  have h : (ModuleCat.free R).map
      (X := ULift.{u} (n.unop ⟶ ((totalSimplexDegree S).obj U.unop).unop))
      (terminal.from _) =
      ModuleCat.freeDesc (M := ModuleCat.of R R) (↾fun _ => (1 : R)) ≫ e.inv := by
    apply ModuleCat.free_hom_ext
    intro a
    rw [ModuleCat.free_map_apply, ModuleCat.comp_apply, ModuleCat.freeDesc_apply]
    change Finsupp.single _ 1 = Finsupp.single _ 1
    congr 1
    exact Subsingleton.elim _ _
  exact congrArg (fun f => f x) h

private lemma componentFreeComplex_evaluation_exact_zero
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (U : S.totalCategoryᵒᵖ) :
    ((ShortComplex.mk ((componentFreeComplex S O).d 1 0)
      ((componentFreeAugmented S O).hom.app (Opposite.op ⦋0⦌))
      (componentFreeComplex_augmentation_comp S O)).map
        (SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U)).Exact := by
  let F := SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U
  let A := ((SimplicialObject.Augmented.whiskering _ _).obj F).obj
    (componentFreeAugmented S O)
  let ed := ((SSet.Augmented.StandardSimplex.extraDegeneracy
    ((totalSimplexDegree S).obj U.unop).unop).map
      (ModuleCat.free (O.obj.obj U))).ofIso
        (componentFreeAugmentedEvaluationIso S O U).symm
  let e := (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso F).app
    (componentFreeSimplicial S O)
  have hz : ((AlgebraicTopology.alternatingFaceMapComplex _).obj A.left).d 1 0 ≫
      A.hom.app (Opposite.op ⦋0⦌) = 0 := by
    exact ((AlgebraicTopology.AlternatingFaceMapComplex.ε.app A).comm 1 0).symm.trans
      Limits.zero_comp
  let T := ShortComplex.mk _ _ hz
  let T' := (ShortComplex.mk ((componentFreeComplex S O).d 1 0)
      ((componentFreeAugmented S O).hom.app (Opposite.op ⦋0⦌))
      (componentFreeComplex_augmentation_comp S O)).map F
  have ei : T' ≅ T := ShortComplex.isoMk
    (HomologicalComplex.Hom.isoApp e 1) (HomologicalComplex.Hom.isoApp e 0) (Iso.refl _)
    (e.hom.comm 1 0)
    (by ext x; rfl)
  exact ShortComplex.exact_of_iso ei.symm (extraDegeneracy_exact_zero A ed)

private lemma componentFreeAugmentation_surjective
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (n : SimplexCategory) (U : S.totalCategoryᵒᵖ) :
    Function.Surjective ((componentFreeAugmentation S O n).app U) := by
  intro x
  change O.obj.obj U at x
  let a : (simplexIndices S n).obj U :=
    ULift.up (SimplexCategory.const n ((totalSimplexDegree S).obj U.unop).unop 0)
  refine ⟨x • ModuleCat.freeMk a, ?_⟩
  change ModuleCat.freeDesc (M := ModuleCat.of (O.obj.obj U) (O.obj.obj U))
      (↾fun _ => (1 : O.obj.obj U)) (x • ModuleCat.freeMk a) = x
  rw [map_smul, ModuleCat.freeDesc_apply]
  change x * 1 = x
  rw [mul_one]

/-- The augmentation is an epimorphism of presheaves of modules, being surjective objectwise. -/
private lemma componentFreeComplex_augmentation_epi_map
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u}) :
    Epi ((SheafOfModules.forget O).map
      ((componentFreeAugmented S O).hom.app (Opposite.op ⦋0⦌))) := by
  constructor
  intro F f g h
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := componentFreeAugmentation_surjective S O ⦋0⦌ U x
  exact congrArg (fun k => k.app U y) h

private lemma componentFreeComplex_augmentation_epi
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u}) :
    Epi ((componentFreeAugmented S O).hom.app (Opposite.op ⦋0⦌)) :=
  (SheafOfModules.forget O).epi_of_epi_map (componentFreeComplex_augmentation_epi_map S O)

private lemma componentFreeComplex_presheaf_exact_positive
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u}) (n : ℕ) :
    (((componentFreeComplex S O).sc' (n + 2) (n + 1) n).map
      (SheafOfModules.forget O)).Exact := by
  apply presheaf_exact_of_evaluation
  intro U
  let F := SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U
  let K := (F.mapHomologicalComplex _).obj (componentFreeComplex S O)
  exact (K.exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp)).1
    (componentFreeComplex_evaluation_exactAt S O U (n + 1) (by omega))

private lemma componentFreeComplex_presheaf_exact_zero
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u}) :
    ((ShortComplex.mk ((componentFreeComplex S O).d 1 0)
      ((componentFreeAugmented S O).hom.app (Opposite.op ⦋0⦌))
      (componentFreeComplex_augmentation_comp S O)).map (SheafOfModules.forget O)).Exact :=
  presheaf_exact_of_evaluation _ (componentFreeComplex_evaluation_exact_zero S O)

private lemma componentFreeComplex_exact_zero
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u}) :
    (ShortComplex.mk ((componentFreeComplex S O).d 1 0)
      ((componentFreeAugmented S O).hom.app (Opposite.op ⦋0⦌))
      (componentFreeComplex_augmentation_comp S O)).Exact := by
  let : HasZeroObject (SheafOfModules.{u} O) := hasZeroObject_of_hasTerminal_object
  let T := ShortComplex.mk ((componentFreeComplex S O).d 1 0)
      ((componentFreeAugmented S O).hom.app (Opposite.op ⦋0⦌))
      (componentFreeComplex_augmentation_comp S O)
  apply exact_of_map_of_exact_next (SheafOfModules.forget O) T (0 : T.X₃ ⟶ 0)
    Limits.comp_zero (componentFreeComplex_presheaf_exact_zero S O)
  have ep := componentFreeComplex_augmentation_epi_map S O
  exact (ShortComplex.exact_iff_epi _
    (show (SheafOfModules.forget O).map (0 : T.X₃ ⟶ 0) = 0 from Functor.map_zero _ _ _)).2 ep

private lemma componentFreeComplex_exact_positive
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (n : ℕ) (hn : 0 < n) : (componentFreeComplex S O).ExactAt n := by
  let : HasZeroObject (SheafOfModules.{u} O) := hasZeroObject_of_hasTerminal_object
  cases n with
  | zero => omega
  | succ k =>
    let K := componentFreeComplex S O
    apply (K.exactAt_iff' (k + 2) (k + 1) k (by simp) (by simp)).2
    cases k with
    | zero =>
      exact exact_of_map_of_exact_next (SheafOfModules.forget O) (K.sc' 2 1 0)
        ((componentFreeAugmented S O).hom.app (Opposite.op ⦋0⦌))
        (componentFreeComplex_augmentation_comp S O)
        (componentFreeComplex_presheaf_exact_positive S O 0)
        (componentFreeComplex_presheaf_exact_zero S O)
    | succ k =>
      exact exact_of_map_of_exact_next (SheafOfModules.forget O)
        (K.sc' (k + 3) (k + 2) (k + 1)) (K.d (k + 1) k) (K.d_comp_d _ _ _)
        (componentFreeComplex_presheaf_exact_positive S O (k + 1))
        (componentFreeComplex_presheaf_exact_positive S O k)

/-- Sections of a module on a component, computed by literal restriction.
This definition imposes no relation between the site and ring universes. -/
public def componentSections (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (F : SheafOfModules.{u} O) :
    Type u :=
  ((componentFunctor S n).op ⋙ F.val.presheaf ⋙ forget AddCommGrpCat.{u}).sections

private noncomputable def componentLowerShriekHomSectionsEquiv
    (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (F : SheafOfModules.{u} O) :
    ((componentModuleLowerShriek
      S O n).obj (SheafOfModules.unit (componentRingSheaf S O n)) ⟶ F) ≃
      componentSections S O n F := by
  let A := componentModuleLowerShriekAdjunction S O n
  let G := (componentModuleRestriction S O n).obj F
  refine (A.homEquiv (SheafOfModules.unit (componentRingSheaf S O n)) F).trans
    ((SheafOfModules.unitHomEquiv G).trans ?_)
  exact Equiv.refl _

/-- The identity-labelled generator on the `n`th component, which is the unit
of the lower-shriek adjunction applied to the section `1` of `Oₙ`. -/
public noncomputable def componentGenerator (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (U : (S.component n)ᵒᵖ) :
    (componentFreePresheaf S O n).obj ((componentFunctor S n).op.obj U) := by
  apply ModuleCat.freeMk
  refine ULift.up ?_
  change n ⟶ ((totalSimplexDegree S).obj ((componentFunctor S n).obj U.unop)).unop
  cases S with
  | mk C => cases C <;> exact 𝟙 n

private def identitySimplexSection (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    ((componentFunctor S n).op ⋙ simplexIndices S n).sections where
  val U := by
    apply ULift.up
    cases S with
    | mk C => cases C <;> exact 𝟙 n
  property := by
    intro U V f
    rcases S with ⟨C | C⟩ <;>
      change ULift.up (𝟙 n ≫ 𝟙 n) = ULift.up (𝟙 n)
    all_goals rw [Category.id_comp]

private lemma componentGenerator_eq (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (U : (S.component n)ᵒᵖ) :
    componentGenerator S O n U = ModuleCat.freeMk ((identitySimplexSection S n).val U) := by
  rcases S with ⟨C | C⟩ <;> rfl

private lemma componentGenerator_naturality (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (U V : (S.component n)ᵒᵖ) (f : U ⟶ V) :
    (componentFreePresheaf S O n).map ((componentFunctor S n).op.map f)
      (componentGenerator S O n U) = componentGenerator S O n V := by
  let I := identitySimplexSection S n
  let k := (componentFunctor S n).op.map f
  calc
    _ = (componentFreePresheaf S O n).map k (ModuleCat.freeMk (I.val U)) :=
      congrArg ((componentFreePresheaf S O n).map k) (componentGenerator_eq S O n U)
    _ = ModuleCat.freeMk ((simplexIndices S n).map k (I.val U)) :=
      (NatTrans.naturality_apply (PresheafOfModules.freeAdjunctionUnit
        (R := O.obj) (F := simplexIndices S n)) k (I.val U)).symm
    _ = ModuleCat.freeMk (I.val V) := congrArg ModuleCat.freeMk (I.property f)
    _ = _ := (componentGenerator_eq S O n V).symm

private def componentGeneratorSection (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory) :
    componentSections S O n (componentFreeSheaf S O n) where
  val U := componentGenerator S O n U
  property := fun f => componentGenerator_naturality S O n _ _ f

private def componentLowerShriekToFree (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory) :
    (componentModuleLowerShriek
      S O n).obj (SheafOfModules.unit (componentRingSheaf S O n)) ⟶ componentFreeSheaf S O n :=
  (componentLowerShriekHomSectionsEquiv S O n _).symm (componentGeneratorSection S O n)

private lemma componentLowerShriekHomSectionsEquiv_naturality
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (n : SimplexCategory) {F G : SheafOfModules.{u} O}
    (f : (componentModuleLowerShriek
      S O n).obj (SheafOfModules.unit (componentRingSheaf S O n)) ⟶ F) (g : F ⟶ G)
    (U : (S.component n)ᵒᵖ) :
    (componentLowerShriekHomSectionsEquiv S O n G (f ≫ g)).val U =
      g.val.app ((componentFunctor S n).op.obj U)
        ((componentLowerShriekHomSectionsEquiv S O n F f).val U) := by
  change (((componentModuleLowerShriekAdjunction S O n).homEquiv _ G (f ≫ g)).val.app U)
    (1 : O.obj.obj ((componentFunctor S n).op.obj U)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private lemma componentLowerShriekToFree_comp_sections
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (n : SimplexCategory) {F : SheafOfModules.{u} O}
    (f : componentFreeSheaf S O n ⟶ F) (U : (S.component n)ᵒᵖ) :
    (componentLowerShriekHomSectionsEquiv S O n F
      (componentLowerShriekToFree S O n ≫ f)).val U =
      f.val.app ((componentFunctor S n).op.obj U) (componentGenerator S O n U) := by
  rw [componentLowerShriekHomSectionsEquiv_naturality]
  change f.val.app _ (((componentLowerShriekHomSectionsEquiv S O n _)
    ((componentLowerShriekHomSectionsEquiv S O n _).symm
      (componentGeneratorSection S O n))).val U) = _
  rw [Equiv.apply_symm_apply]
  rfl

private def freeBasis (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (X : S.totalCategoryᵒᵖ) (a : (simplexIndices S n).obj X) :
    (componentFreePresheaf S O n).obj X :=
  ModuleCat.freeMk a

private lemma freeBasis_map (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    {X Y : S.totalCategoryᵒᵖ} (k : X ⟶ Y)
    (a : (simplexIndices S n).obj X) :
    (componentFreePresheaf S O n).map k (freeBasis S O n X a) =
      freeBasis S O n Y ((simplexIndices S n).map k a) :=
  (NatTrans.naturality_apply
    (PresheafOfModules.freeAdjunctionUnit (R := O.obj)
      (F := simplexIndices S n)) k a).symm


private def freeHomToSimplex (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (F : SheafOfModules.{u} O) (f : componentFreeSheaf S O n ⟶ F) :
    simplexIndices S n ⟶ F.val.presheaf ⋙ forget AddCommGrpCat.{u} where
  app X := ↾fun a => f.val.app X (freeBasis S O n X a)
  naturality := by
    intro X Y k
    ext a
    change f.val.app Y (freeBasis S O n Y ((simplexIndices S n).map k a)) =
      F.val.map k (f.val.app X (freeBasis S O n X a))
    rw [← freeBasis_map]
    exact PresheafOfModules.naturality_apply f.val k _

private def freeDescLinear (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (F : SheafOfModules.{u} O)
    (f : simplexIndices S n ⟶ F.val.presheaf ⋙ forget AddCommGrpCat.{u})
    (X : S.totalCategoryᵒᵖ) : (componentFreePresheaf S O n).obj X ⟶ F.val.obj X := by
  letI := (F.val.obj X).isModule
  exact ModuleCat.ofHom (Finsupp.linearCombination (M := F.val.obj X) (O.obj.obj X)
    (fun a : (simplexIndices S n).obj X => (f.app X a : F.val.obj X)))

private lemma freeDescLinear_basis (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (F : SheafOfModules.{u} O)
    (f : simplexIndices S n ⟶ F.val.presheaf ⋙ forget AddCommGrpCat.{u})
    (X : S.totalCategoryᵒᵖ) (a : (simplexIndices S n).obj X) :
    freeDescLinear S O n F f X (freeBasis S O n X a) = f.app X a := by
  let := (F.val.obj X).isModule
  change (Finsupp.linearCombination (M := F.val.obj X) (O.obj.obj X)
    (fun b : (simplexIndices S n).obj X => f.app X b)) (Finsupp.single a 1) = f.app X a
  rw [Finsupp.linearCombination_single, one_smul]

private lemma freeBasis_ext (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (X : S.totalCategoryᵒᵖ) {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {σ : O.obj.obj X →+* R}
    {f g : (componentFreePresheaf S O n).obj X →ₛₗ[σ] M}
    (h : ∀ a, f (freeBasis S O n X a) = g (freeBasis S O n X a)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using Finsupp.induction_linear with
  | zero => exact f.map_zero.trans g.map_zero.symm
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | single a r =>
    have hs : (Finsupp.single a r : (componentFreePresheaf S O n).obj X) =
        r • freeBasis S O n X a := by
      change Finsupp.single a r = r • Finsupp.single a 1
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smulₛₗ, map_smulₛₗ, h]

private def freeHomOfSimplex (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (F : SheafOfModules.{u} O)
    (f : simplexIndices S n ⟶ F.val.presheaf ⋙ forget AddCommGrpCat.{u}) :
    componentFreeSheaf S O n ⟶ F := ⟨{
  app := freeDescLinear S O n F f
  naturality := by
    intro X Y k
    apply ModuleCat.hom_ext
    apply freeBasis_ext S O n X
    intro a
    change freeDescLinear S O n F f Y
        ((componentFreePresheaf S O n).map k (freeBasis S O n X a)) =
      F.val.map k (freeDescLinear S O n F f X (freeBasis S O n X a))
    rw [freeBasis_map, freeDescLinear_basis, freeDescLinear_basis]
    exact NatTrans.naturality_apply f k a }⟩

private def freeHomSimplexEquiv (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
    (F : SheafOfModules.{u} O) :
    (componentFreeSheaf S O n ⟶ F) ≃
      (simplexIndices S n ⟶ F.val.presheaf ⋙ forget AddCommGrpCat.{u}) where
  toFun := freeHomToSimplex S O n F
  invFun := freeHomOfSimplex S O n F
  left_inv f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply freeBasis_ext S O n X
    intro a
    exact freeDescLinear_basis S O n F (freeHomToSimplex S O n F f) X a
  right_inv f := by
    ext X a
    exact freeDescLinear_basis S O n F f X a


private lemma componentLowerShriekToFree_isIso
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (n : SimplexCategory) : IsIso (componentLowerShriekToFree S O n) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro F
  let G : Sheaf S.totalTopology (Type u) :=
    ⟨F.val.presheaf ⋙ forget AddCommGrpCat.{u},
      Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.isSheaf⟩
  let e := freeHomSimplexEquiv S O n F
  let e' := componentLowerShriekHomSectionsEquiv S O n F
  have hb := (simplexHomSection_bijective S G n).comp e.bijective
  have he (f : componentFreeSheaf S O n ⟶ F) :
      e' (componentLowerShriekToFree S O n ≫ f) =
        simplexHomComponentSection S G.obj (e f) (𝟙 n) := by
    apply Subtype.ext
    funext U
    refine (componentLowerShriekToFree_comp_sections S O n f U).trans ?_
    rcases S with ⟨C | C⟩ <;> rfl
  constructor
  · intro f g h
    apply hb.injective
    change simplexHomComponentSection S G.obj (e f) (𝟙 n) =
      simplexHomComponentSection S G.obj (e g) (𝟙 n)
    exact (he f).symm.trans ((congrArg e' h).trans (he g))
  · intro f
    obtain ⟨g, hg⟩ := hb.surjective (e' f)
    exact ⟨g, e'.injective ((he g).trans hg)⟩

/-- The canonical augmented resolution by the modules `gₙ! Oₙ`. The underlying
presheaves are the explicit free modules on simplex labels, the differentials
are alternating sums of precomposition maps, and augmentation sends each
label to `1`. The component-section equivalence records the lower-shriek
universal property and is pinned to evaluation at the identity generator. -/
public structure SimplicialModuleResolution (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) where
  /-- The augmented complex before adjoining its degree `-1` term. -/
  complex : ChainComplex
    (SheafOfModules.{u} O) ℕ
  /-- The termwise identification with the explicit lower-shriek presheaf. -/
  degreeIso (n : ℕ) : (complex.X n).val ≅ componentFreePresheaf S O ⦋n⦌
  /-- Under the termwise identifications, the differential is the alternating
  sum of the maps labelled by the standard cofaces. -/
  differential_eq (n : ℕ) :
    (degreeIso (n + 1)).inv ≫ (complex.d (n + 1) n).val ≫ (degreeIso n).hom =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • componentFreeMap S O (SimplexCategory.δ i)
  /-- The universal property `Hom(gₙ! Oₙ, F) ≃ Γ(Cₙ, Fₙ)`. -/
  homSectionsEquiv (n : ℕ)
      (F : SheafOfModules.{u} O) :
    (complex.X n ⟶ F) ≃ componentSections S O ⦋n⦌ F
  /-- The universal-property bijection evaluates at the identity-labelled
  generator. -/
  homSectionsEquiv_apply (n : ℕ)
      (F : SheafOfModules.{u} O)
      (f : complex.X n ⟶ F) (U : (S.component ⦋n⦌)ᵒᵖ) :
    (homSectionsEquiv n F f).val U =
      (((degreeIso n).inv ≫ f.val).app ((componentFunctor S ⦋n⦌).op.obj U))
        (componentGenerator S O ⦋n⦌ U)
  /-- Augmentation to the structure sheaf as a module over itself. -/
  augmentation : complex.X 0 ⟶
    SheafOfModules.unit O
  /-- Augmentation is the canonical map sending each label to `1`. -/
  augmentation_eq : (degreeIso 0).inv ≫ augmentation.val =
    componentFreeAugmentation S O ⦋0⦌
  /-- The augmentation composed with the first differential is zero. -/
  augmentation_comp : complex.d 1 0 ≫ augmentation = 0
  /-- The complex is exact in every positive degree. -/
  exact_positive (n : ℕ) (hn : 0 < n) : complex.ExactAt n
  /-- The sequence `X₁ ⟶ X₀ ⟶ O` given by the first differential and the augmentation is
  exact. -/
  exact_zero : (ShortComplex.mk (complex.d 1 0) augmentation augmentation_comp).Exact
  /-- The augmentation is an epimorphism. -/
  augmentation_epi : Epi augmentation

namespace SimplicialModuleResolution
variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology RingCat.{u}}

/-- The canonical simplex map on the sheaf terms of the resolution. -/
public noncomputable def faceMap (D : SimplicialModuleResolution S O)
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) : D.complex.X n ⟶ D.complex.X m :=
  ⟨(D.degreeIso n).hom ≫ componentFreeMap S O φ ≫ (D.degreeIso m).inv⟩

/-- The sheaf differential is the alternating sum of the canonical face maps. -/
public theorem differential_eq_sum_faceMap (D : SimplicialModuleResolution S O) (n : ℕ) :
    D.complex.d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • D.faceMap (SimplexCategory.δ i) := by
  apply (SheafOfModules.forget _).map_injective
  rw [Functor.map_sum]
  simp only [Functor.map_zsmul]
  change (D.complex.d (n + 1) n).val =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((D.degreeIso (n + 1)).hom ≫ componentFreeMap S O (SimplexCategory.δ i) ≫
        (D.degreeIso n).inv)
  apply (cancel_epi (D.degreeIso (n + 1)).inv).mp
  apply (cancel_mono (D.degreeIso n).hom).mp
  simpa only [Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using D.differential_eq n

end SimplicialModuleResolution

/-- The explicit simplicial resolution, with each term literally the actual
component-module lower shriek of Tag 0D72. Thus the resolution can
be used with constructions expressed directly in terms of `gₙ! Oₙ`. -/
public structure SimplicialModuleResolutionActual (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) extends
    SimplicialModuleResolution S O where
  /-- The degree-`n` term is exactly the lower-shriek image of the structure
  sheaf on the `n`th component, not merely an abstract free-module model. -/
  lowerShriekDegreeEq (n : ℕ) :
    complex.X n =
      (componentModuleLowerShriek
        S O ⦋n⦌).obj
        (SheafOfModules.unit (componentRingSheaf S O ⦋n⦌))

private def simplicialModuleResolutionOfIsIso
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (h : ∀ n, IsIso (componentLowerShriekToFree S O ⦋n⦌)) :
    SimplicialModuleResolutionActual S O := by
  let D := componentFreeComplex S O
  let L (n : ℕ) :=
    (componentModuleLowerShriek
      S O ⦋n⦌).obj (SheafOfModules.unit (componentRingSheaf S O ⦋n⦌))
  let e (n : ℕ) : L n ≅ D.X n := @asIso _ _ _ _ (componentLowerShriekToFree S O ⦋n⦌) (h n)
  let K : ChainComplex (SheafOfModules.{u} O) ℕ :=
    { X := L
      d := fun i j => (e i).hom ≫ D.d i j ≫ (e j).inv
      shape := by intro i j hij; rw [D.shape i j hij]; simp
      d_comp_d' := by intro i j k hij hjk; simp [Category.assoc] }
  let ei : K ≅ D := HomologicalComplex.Hom.isoOfComponents e
    (by intro i j hij; simp [K, Category.assoc])
  let ε : D.X 0 ⟶ SheafOfModules.unit O := ⟨componentFreeAugmentation S O ⦋0⦌⟩
  have hε : D.d 1 0 ≫ ε = 0 := componentFreeComplex_augmentation_comp S O
  have hKε : K.d 1 0 ≫ ((e 0).hom ≫ ε) = 0 := by
    dsimp [K]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hε, Limits.comp_zero]
  refine
    { complex := K
      degreeIso := fun n => (SheafOfModules.forget O).mapIso (e n)
      differential_eq := ?_
      homSectionsEquiv := fun n F => componentLowerShriekHomSectionsEquiv S O ⦋n⦌ F
      homSectionsEquiv_apply := ?_
      augmentation := (e 0).hom ≫ ε
      augmentation_eq := ?_
      augmentation_comp := hKε
      exact_positive := fun n hn =>
        HomologicalComplex.ExactAt.of_iso (e := ei.symm)
          (componentFreeComplex_exact_positive S O n hn)
      exact_zero := ?_
      augmentation_epi := ?_
      lowerShriekDegreeEq := fun n => rfl }
  · intro n
    refine Eq.trans ?_ (componentFreeComplex_d S O n)
    change (SheafOfModules.forget O).map ((e (n + 1)).inv) ≫
        (SheafOfModules.forget O).map (K.d (n + 1) n) ≫
        (SheafOfModules.forget O).map ((e n).hom) = _
    simp only [← (SheafOfModules.forget O).map_comp]
    congr 1
    simp [K, D, Category.assoc]
  · intro n F f U
    have hp := componentLowerShriekToFree_comp_sections S O ⦋n⦌ ((e n).inv ≫ f) U
    have hcomp : componentLowerShriekToFree S O ⦋n⦌ ≫ (e n).inv ≫ f = f := by
      change (e n).hom ≫ (e n).inv ≫ f = f
      simp only [Iso.hom_inv_id_assoc]
    rw [hcomp] at hp
    exact hp
  · change (SheafOfModules.forget O).map ((e 0).inv) ≫
        (SheafOfModules.forget O).map ((e 0).hom ≫ ε) = _
    rw [← (SheafOfModules.forget O).map_comp, Iso.inv_hom_id_assoc]
    rfl
  · let T := ShortComplex.mk (K.d 1 0) ((e 0).hom ≫ ε) hKε
    let T' := ShortComplex.mk (D.d 1 0) ε hε
    let et : T ≅ T' := ShortComplex.isoMk (e 1) (e 0) (Iso.refl _)
      (by simp [T, T', K, Category.assoc]) (by simp [T, T'])
    exact ShortComplex.exact_of_iso et.symm (componentFreeComplex_exact_zero S O)
  · have : Epi ε := componentFreeComplex_augmentation_epi S O
    infer_instance

private theorem nonempty_simplicialModuleResolution_of_isIso
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
    (h : ∀ n, IsIso (componentLowerShriekToFree S O ⦋n⦌)) :
    Nonempty (SimplicialModuleResolutionActual S O) :=
  ⟨simplicialModuleResolutionOfIsIso S O h⟩

/-- **Stacks 0D9B.** There is a complex of modules over the structure sheaf of the total
simplicial site whose term in degree `n` is the lower-shriek image `g_{n!}𝒪_n` of the `n`-th
component structure sheaf, whose differentials are the canonical alternating face maps, and
which is a resolution of the structure sheaf. -/
@[stacks 0D9B]
public theorem nonempty_simplicialModuleResolution (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) :
    Nonempty (SimplicialModuleResolutionActual S O) :=
  nonempty_simplicialModuleResolution_of_isIso S O
    (fun n => componentLowerShriekToFree_isIso S O ⦋n⦌)

/-- **The resolution of Stacks 0D9B with its augmentation adjoint to the identity.** There is a
resolution `… → g_{1!}O_1 → g_{0!}O_0 → O` whose augmentation `g_{0!}O_0 ⟶ O` is the counit of
`g_{0!} ⊣ g_0^*` at the structure sheaf: its transpose along that adjunction is the identity of
`O_0`, the restriction of `O` to the component of degree zero.

For an arbitrary resolution the augmentation is pinned only through the resolution's own
identification of `g_{0!}O_0` with the free model, which may differ from the one the adjunction
induces by an automorphism; the resolution constructed for Stacks 0D9B uses the identification
the adjunction induces, and this records it. -/
public theorem exists_simplicialModuleResolutionActual_homEquiv_augmentation
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u}) :
    ∃ D : SimplicialModuleResolutionActual S O,
      (componentModuleLowerShriekAdjunction S O ⦋0⦌).homEquiv _ _
          (eqToHom (D.lowerShriekDegreeEq 0).symm ≫ D.augmentation) =
        𝟙 (SheafOfModules.unit (componentRingSheaf S O ⦋0⦌)) := by
  refine ⟨simplicialModuleResolutionOfIsIso S O
    (fun n => componentLowerShriekToFree_isIso S O ⦋n⦌), ?_⟩
  apply (SheafOfModules.unitHomEquiv _).injective
  apply Subtype.ext
  funext U
  have h := componentLowerShriekToFree_comp_sections S O ⦋0⦌
    (F := SheafOfModules.unit O) ⟨componentFreeAugmentation S O ⦋0⦌⟩ U
  refine Eq.trans ?_ (h.trans ?_)
  · change (componentLowerShriekHomSectionsEquiv S O ⦋0⦌ _
      (𝟙 _ ≫ componentLowerShriekToFree S O ⦋0⦌ ≫
        ⟨componentFreeAugmentation S O ⦋0⦌⟩)).val U = _
    rw [Category.id_comp]
  · rw [componentGenerator_eq]
    change ModuleCat.freeDesc _ (ModuleCat.freeMk _) = _
    rw [ModuleCat.freeDesc_apply]
    rfl

end CategoryTheory.SimplicialSiteSituation

end
