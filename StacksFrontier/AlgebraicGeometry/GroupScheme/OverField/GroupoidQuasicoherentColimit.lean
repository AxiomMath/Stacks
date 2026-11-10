module

public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Filtered
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidInvariantSubmodule

/-!
# Quasi-coherent modules on a groupoid scheme as colimits of their bounded submodules

Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t` flat.  Stacks 077U labels three
assertions: a cardinal `κ` attached to the groupoid scheme, the directedness of the system of
`κ`-generated quasi-coherent submodules of a quasi-coherent module `(F, α)` on it, and the fact
that the canonical cocone of that system is colimiting.  All three are proved here.

A submodule of `(F, α)` is a subobject in the category
`Stacks.Groupoids.GroupoidScheme.QuasicoherentModule G`, which is abelian because `s` and `t` are
flat (Stacks 077S), and it is called `κ`-generated when the underlying `𝒪_U`-module is.  The
cardinal is the maximum of the cardinals Gabber's theorem for a single scheme (Stacks 077N)
attaches to the object scheme and to the arrow scheme.

## Main definitions

* `cardinalBound`: the cardinal, the first assertion of Stacks 077U.
* `CardinalGeneratedSubobject`, `cardinalGeneratedSubobjectFunctor` and
  `cardinalGeneratedSubobjectCocone`: the system of `κ`-generated submodules of `(F, α)` and its
  canonical cocone.

## Main results

* `isColimit_of_forget`: a cocone of quasi-coherent modules on a groupoid scheme is colimiting as
  soon as it is colimiting on the underlying modules on the object scheme.
* `isFiltered_cardinalGeneratedSubobject` and
  `cardinalGeneratedSubobject_isFiltered`: **the directedness assertion of Stacks 077U**, for an
  arbitrary infinite cardinal and at `cardinalBound G`.
* `isColimit_cardinalGeneratedSubobjectCocone`: **the colimit assertion of Stacks 077U**.

## Route

Directedness is the source's argument: the join of two subobjects is the image of their
coproduct, so what has to be checked is that `κ`-generation of the underlying module survives a
binary coproduct and an epimorphic image.  Both are already available for `𝒪_U`-modules
(`Stacks.AlgebraicGeometry.CardinalGeneration.isCardinalGenerated_coprod` and
`isCardinalGenerated_of_epi`), and they transfer because the forgetful functor to `𝒪_U`-modules
preserves finite colimits — it preserves every cokernel, since cokernels of quasi-coherent
modules on a groupoid scheme are computed on the underlying modules — and therefore preserves
binary coproducts and epimorphisms.

For the colimit the comparison map is pushed through the forgetful functor, which also reflects
colimits.  On `𝒪_U`-modules the argument is the one used for Stacks 077N: the diagram of
underlying modules is a diagram of subobjects of `F`, so
`CategoryTheory.IsGrothendieckAbelian.mono_of_isColimit_monoOver` makes the comparison map a
monomorphism, and
`Stacks.AlgebraicGeometry.CardinalGeneration.isIso_of_mono_of_locallySurjective` upgrades it to
an isomorphism once it is locally surjective on sections.  Local surjectivity is
`Stacks.AlgebraicGeometry.GroupoidCardinalGeneration.exists_invariantObject_of_section`: every
section of `F` lies in a `κ`-generated submodule of `(F, α)`, by the invariant closure
construction.

## Implementation notes

The index category is only essentially small — subobjects of a quasi-coherent module on a
groupoid scheme do not form a `Type u` — whereas both
`CategoryTheory.IsGrothendieckAbelian.mono_of_isColimit_monoOver` and the preservation of
colimits by pullback of modules want a small category.  The diagram is therefore replaced by its
small model, with `CategoryTheory.Limits.IsColimit.ofWhiskerEquivalence` transporting the
conclusion back, exactly as in the proof of Stacks 077N.

`monoOverForgetDiagram` records the diagram of underlying modules as a diagram in
`CategoryTheory.MonoOver F`; its functoriality laws hold because `CategoryTheory.MonoOver` is a
thin category.  Composing it with the two forgetful functors gives the diagram of underlying
modules back definitionally, which is what lets the Grothendieck-abelian lemma be applied to the
colimit cocone of the image under the forgetful functor of the canonical cocone.

## References

* [Stacks Project, Tag 077U](https://stacks.math.columbia.edu/tag/077U)
* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
* [Stacks Project, Tag 077S](https://stacks.math.columbia.edu/tag/077S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Groupoids Stacks.Groupoids.GroupoidScheme
open Stacks.AlgebraicGeometry.CardinalGeneration

universe u

attribute [local instance] AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat

namespace Stacks.AlgebraicGeometry.GroupoidCardinalGeneration

/-! ### The cardinal -/

/-- **The cardinal of Stacks 077U.**  For a groupoid scheme it is the maximum of the cardinals
Gabber's theorem attaches to the object scheme and to the arrow scheme; the closure construction
producing the bounded submodules uses exactly that it is infinite and dominates the numbers of
affine opens of the two schemes. -/
@[stacks 077U "cardinal"]
def cardinalBound {S : Scheme.{u}} (G : GroupoidScheme S) : Cardinal.{u} :=
  CardinalGeneration.cardinalBound G.objects.left ⊔
    CardinalGeneration.cardinalBound G.arrows.left

/-- The cardinal of Stacks 077U is infinite. -/
theorem aleph0_le_cardinalBound {S : Scheme.{u}} (G : GroupoidScheme S) :
    Cardinal.aleph0 ≤ cardinalBound G :=
  le_sup_of_le_left (CardinalGeneration.aleph0_le_cardinalBound _)

/-- The cardinal of Stacks 077U dominates the number of affine opens of the object scheme. -/
theorem mk_affineOpens_objects_le_cardinalBound {S : Scheme.{u}} (G : GroupoidScheme S) :
    Cardinal.mk G.objects.left.affineOpens ≤ cardinalBound G :=
  le_sup_of_le_left (CardinalGeneration.mk_affineOpens_le_cardinalBound _)

/-- The cardinal of Stacks 077U dominates the number of affine opens of the arrow scheme. -/
theorem mk_affineOpens_arrows_le_cardinalBound {S : Scheme.{u}} (G : GroupoidScheme S) :
    Cardinal.mk G.arrows.left.affineOpens ≤ cardinalBound G :=
  le_sup_of_le_right (CardinalGeneration.mk_affineOpens_le_cardinalBound _)

section Flat

variable {S : Scheme.{u}} {G : GroupoidScheme S} [Flat G.source.left] [Flat G.target.left]

/-! ### Exactness properties of the forgetful functor -/

/-- The forgetful functor to modules on the object scheme preserves finite limits: it is additive
and preserves every kernel, because kernels are computed on the underlying modules. -/
instance preservesFiniteLimits_forget :
    PreservesFiniteLimits (QuasicoherentModule.forget G) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- The forgetful functor to modules on the object scheme preserves finite colimits: it is
additive and preserves every cokernel, because cokernels are computed on the underlying
modules. -/
instance preservesFiniteColimits_forget :
    PreservesFiniteColimits (QuasicoherentModule.forget G) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- The forgetful functor to modules on the object scheme preserves monomorphisms. -/
instance preservesMonomorphisms_forget :
    (QuasicoherentModule.forget G).PreservesMonomorphisms :=
  inferInstance

/-- The forgetful functor to modules on the object scheme preserves epimorphisms. -/
instance preservesEpimorphisms_forget :
    (QuasicoherentModule.forget G).PreservesEpimorphisms :=
  inferInstance

/-- **A cocone of quasi-coherent modules on a groupoid scheme is colimiting as soon as it is
colimiting on the underlying modules on the object scheme.**  The descent morphism of the apex is
determined by those of the diagram, so the morphism of underlying modules out of the colimit
automatically intertwines the descent morphisms. -/
def isColimit_of_forget {J : Type u} [SmallCategory J] {D : J ⥤ QuasicoherentModule G}
    (c : Cocone D) (hc : IsColimit ((QuasicoherentModule.forget G).mapCocone c)) :
    IsColimit c where
  desc d :=
    { hom := hc.desc ((QuasicoherentModule.forget G).mapCocone d)
      comm := by
        apply (isColimitOfPreserves (Scheme.Modules.pullback G.target.left) hc).hom_ext
        intro i
        change (Scheme.Modules.pullback G.target.left).map (c.ι.app i).hom ≫
            c.pt.alpha ≫ (Scheme.Modules.pullback G.source.left).map
              (hc.desc ((QuasicoherentModule.forget G).mapCocone d)) =
          (Scheme.Modules.pullback G.target.left).map (c.ι.app i).hom ≫
            (Scheme.Modules.pullback G.target.left).map
              (hc.desc ((QuasicoherentModule.forget G).mapCocone d)) ≫ d.pt.alpha
        have hiC := (c.ι.app i).comm
        dsimp only [Functor.const_obj_obj] at hiC
        rw [← Category.assoc, ← hiC, Category.assoc, ← Functor.map_comp,
          ← Functor.map_comp_assoc,
          show (c.ι.app i).hom ≫ hc.desc ((QuasicoherentModule.forget G).mapCocone d) =
            (d.ι.app i).hom from hc.fac _ i]
        exact (d.ι.app i).comm }
  fac d i := QuasicoherentModule.Hom.ext (hc.fac _ i)
  uniq d k hk := QuasicoherentModule.Hom.ext <| hc.hom_ext fun i ↦
    (congrArg QuasicoherentModule.Hom.hom (hk i)).trans
      (hc.fac ((QuasicoherentModule.forget G).mapCocone d) i).symm

/-! ### The system of bounded submodules -/

/-- The property of a subobject of a quasi-coherent module on a groupoid scheme that its
underlying module on the object scheme is generated by at most `κ` local sections. -/
def cardinalGeneratedSubobjectProperty (M : QuasicoherentModule G) (κ : Cardinal.{u}) :
    ObjectProperty (Subobject M) :=
  fun P ↦ CardinalGeneration.IsCardinalGenerated.{u, u, u} (P : QuasicoherentModule G).module κ

/-- The category of `κ`-generated quasi-coherent submodules of a quasi-coherent module on a
groupoid scheme. -/
abbrev CardinalGeneratedSubobject (M : QuasicoherentModule G) (κ : Cardinal.{u}) :=
  (cardinalGeneratedSubobjectProperty M κ).FullSubcategory

/-- The diagram of all `κ`-generated quasi-coherent submodules of `M`. -/
def cardinalGeneratedSubobjectFunctor (M : QuasicoherentModule G) (κ : Cardinal.{u}) :
    CardinalGeneratedSubobject M κ ⥤ QuasicoherentModule G :=
  (cardinalGeneratedSubobjectProperty M κ).ι ⋙ Subobject.underlying

/-- The canonical cocone from all `κ`-generated quasi-coherent submodules of `M` to `M`. -/
def cardinalGeneratedSubobjectCocone (M : QuasicoherentModule G) (κ : Cardinal.{u}) :
    Cocone (cardinalGeneratedSubobjectFunctor M κ) :=
  Cocone.mk M
    { app := fun P ↦ P.obj.arrow
      naturality := fun {_ _} h ↦ Subobject.underlying_arrow h.hom }

/-! ### Smallness of the system -/

omit [Flat G.target.left] in
/-- A subobject of a quasi-coherent module on a groupoid scheme is determined by the subobject of
the underlying module it cuts out: an inclusion of the underlying subobjects intertwines the
descent morphisms automatically, by cancelling the monomorphism obtained from the larger one by
pullback along the source. -/
private theorem le_of_mk_hom_le (M : QuasicoherentModule G) (A B : Subobject M)
    [Mono A.arrow.hom] [Mono B.arrow.hom]
    (h : Subobject.mk A.arrow.hom ≤ Subobject.mk B.arrow.hom) : A ≤ B := by
  have : Mono ((Scheme.Modules.pullback G.source.left).map B.arrow.hom) := Functor.map_mono _ _
  have hfac : Subobject.ofMkLEMk A.arrow.hom B.arrow.hom h ≫ B.arrow.hom = A.arrow.hom :=
    Subobject.ofMkLEMk_comp h
  refine Subobject.le_of_comm
    { hom := Subobject.ofMkLEMk A.arrow.hom B.arrow.hom h
      comm := ?_ } (QuasicoherentModule.Hom.ext hfac)
  refine (cancel_mono ((Scheme.Modules.pullback G.source.left).map B.arrow.hom)).1 ?_
  simp only [Category.assoc]
  rw [B.arrow.comm, ← Functor.map_comp_assoc, hfac, ← A.arrow.comm, ← Functor.map_comp, hfac]

/-- The subobjects of a quasi-coherent module on a groupoid scheme with flat source and target
form a `Type u`: they are determined by the subobjects of the underlying module they cut out, and
modules on a scheme are well-powered. -/
instance small_subobject (M : QuasicoherentModule G) : Small.{u} (Subobject M) := by
  have hm : ∀ P : Subobject M, Mono P.arrow.hom :=
    fun P ↦ (QuasicoherentModule.forget G).map_mono P.arrow
  refine small_of_injective
    (f := fun P : Subobject M ↦ @Subobject.mk _ _ _ _ P.arrow.hom (hm P)) fun P Q hPQ ↦ ?_
  have := hm P
  have := hm Q
  exact le_antisymm (le_of_mk_hom_le M P Q hPQ.le) (le_of_mk_hom_le M Q P hPQ.ge)

/-! ### Directedness -/

/-- The zero module on a scheme is `κ`-generated for every `κ ≥ 1`: it is a quotient of the
structure sheaf, every morphism to a zero object being an epimorphism. -/
theorem isCardinalGenerated_of_isZero (X : Scheme.{u}) {κ : Cardinal.{u}} (hκ : 1 ≤ κ)
    (Z : X.Modules) (hZ : IsZero Z) : CardinalGeneration.IsCardinalGenerated.{u, u, u} Z κ := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let p : O ⟶ Z := Zero.zero
  exact @CardinalGeneration.isCardinalGenerated_of_epi _ _ _ _ _ _ _ _ _ p (hZ.epi p) κ
    (CardinalGeneration.isCardinalGenerated_unit X hκ)

/-- **The directedness assertion of Stacks 077U**, for an arbitrary infinite cardinal.  The
`κ`-generated quasi-coherent submodules of a quasi-coherent module `(F, α)` on a groupoid scheme
with flat source and target form a filtered system: the join of two of them is the image in
`(F, α)` of their coproduct, whose underlying module is the coproduct of the two underlying
modules and hence, `κ` being infinite, again `κ`-generated. -/
theorem isFiltered_cardinalGeneratedSubobject (M : QuasicoherentModule G) {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) : IsFiltered (CardinalGeneratedSubobject M κ) := by
  let P := cardinalGeneratedSubobjectProperty M κ
  refine { cocone_objs := ?_, cocone_maps := ?_, nonempty := ?_ }
  · intro A B
    have hSgen : CardinalGeneration.IsCardinalGenerated.{u, u, u}
        ((QuasicoherentModule.forget G).obj
          ((A.1 : QuasicoherentModule G) ⨿ (B.1 : QuasicoherentModule G))) κ := by
      refine CardinalGeneration.isCardinalGenerated_of_iso κ
        (PreservesColimitPair.iso (QuasicoherentModule.forget G)
          (A.1 : QuasicoherentModule G) (B.1 : QuasicoherentModule G)) ?_
      exact CardinalGeneration.isCardinalGenerated_coprod hκ A.2 B.2
    let f : (A.1 : QuasicoherentModule G) ⨿ (B.1 : QuasicoherentModule G) ⟶ M :=
      coprod.desc A.1.arrow B.1.arrow
    let I : Subobject M := imageSubobject f
    have hp : Epi (factorThruImageSubobject f) := by
      dsimp only [factorThruImageSubobject]
      apply epi_comp
    have hgen : CardinalGeneration.IsCardinalGenerated.{u, u, u}
        (I : QuasicoherentModule G).module κ :=
      @CardinalGeneration.isCardinalGenerated_of_epi _ _ _ _ _ _ _ _ _
        ((QuasicoherentModule.forget G).map (factorThruImageSubobject f))
        (@Functor.map_epi _ _ _ _ (QuasicoherentModule.forget G) _ _ _ _ hp) κ hSgen
    have hA : A.1 ≤ I := by
      refine Subobject.le_of_comm (coprod.inl ≫ factorThruImageSubobject f) ?_
      change (coprod.inl ≫ factorThruImageSubobject f) ≫ I.arrow = A.1.arrow
      rw [Category.assoc, imageSubobject_arrow_comp]
      exact coprod.inl_desc _ _
    have hB : B.1 ≤ I := by
      refine Subobject.le_of_comm (coprod.inr ≫ factorThruImageSubobject f) ?_
      change (coprod.inr ≫ factorThruImageSubobject f) ≫ I.arrow = B.1.arrow
      rw [Category.assoc, imageSubobject_arrow_comp]
      exact coprod.inr_desc _ _
    exact ⟨⟨I, hgen⟩, P.homMk (homOfLE hA), P.homMk (homOfLE hB), trivial⟩
  · exact fun A B k l ↦ ⟨B, 𝟙 B, P.hom_ext (Subsingleton.elim _ _)⟩
  · exact ⟨⟨⊥, isCardinalGenerated_of_isZero G.objects.left (Cardinal.one_le_aleph0.trans hκ) _
      (IsZero.of_iso ((QuasicoherentModule.forget G).map_isZero (isZero_zero _))
        ((QuasicoherentModule.forget G).mapIso (Subobject.botCoeIsoZero (B := M))))⟩⟩

/-- **Stacks 077U, the directedness assertion**, at the cardinal the tag attaches to the groupoid
scheme. -/
@[stacks 077U "directedness"]
instance cardinalGeneratedSubobject_isFiltered (M : QuasicoherentModule G) :
    IsFiltered (CardinalGeneratedSubobject M (cardinalBound G)) :=
  isFiltered_cardinalGeneratedSubobject M (aleph0_le_cardinalBound G)

/-! ### The colimit -/

/-- The index category replaced by a `Type u`-small model of it. -/
abbrev smallIndexEquiv (M : QuasicoherentModule G) (κ : Cardinal.{u}) :
    SmallModel (CardinalGeneratedSubobject M κ) ≌ CardinalGeneratedSubobject M κ :=
  (equivSmallModel (CardinalGeneratedSubobject M κ)).symm

/-- The system of bounded submodules of `M`, read as a diagram of subobjects of the underlying
module of `M`.  Functoriality holds because `CategoryTheory.MonoOver` is a thin category. -/
def monoOverForgetDiagram (M : QuasicoherentModule G) (κ : Cardinal.{u}) :
    CardinalGeneratedSubobject M κ ⥤ MonoOver M.module where
  obj P := MonoOver.mk ((QuasicoherentModule.forget G).map P.obj.arrow)
  map {P Q} h := MonoOver.homMk
    ((QuasicoherentModule.forget G).map (Subobject.underlying.map
      ((cardinalGeneratedSubobjectProperty M κ).ι.map h)))
    (by
      change (QuasicoherentModule.forget G).map (Subobject.underlying.map
            ((cardinalGeneratedSubobjectProperty M κ).ι.map h)) ≫
          (QuasicoherentModule.forget G).map Q.obj.arrow =
        (QuasicoherentModule.forget G).map P.obj.arrow
      exact ((QuasicoherentModule.forget G).map_comp _ _).symm.trans
        (congrArg (QuasicoherentModule.forget G).map (Subobject.underlying_arrow _)))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The `MonoOver`-valued diagram of bounded submodules over the small model of the index
category. -/
def smallMonoOverDiagram (M : QuasicoherentModule G) (κ : Cardinal.{u}) :
    SmallModel (CardinalGeneratedSubobject M κ) ⥤ MonoOver M.module :=
  (smallIndexEquiv M κ).functor ⋙ monoOverForgetDiagram M κ

/-- **The colimit assertion of Stacks 077U, reduced to local membership.**  If every section of
the underlying module of `M` is, near each point, a section of a `κ`-generated submodule of `M`,
then the canonical cocone of the `κ`-generated submodules of `M` is colimiting. -/
def isColimit_cocone_of_locally_mem (M : QuasicoherentModule G) (κ : Cardinal.{u})
    [IsFiltered (CardinalGeneratedSubobject M κ)]
    (h : ∀ (O : G.objects.left.Opens) (z : Γ(M.module, O)) (x : G.objects.left), x ∈ O →
      ∃ V : G.objects.left.Opens, ∃ hVO : V ≤ O, x ∈ V ∧
        ∃ Q : CardinalGeneratedSubobject M κ,
          M.module.presheaf.map (homOfLE hVO).op z ∈
            Set.range (((QuasicoherentModule.forget G).map Q.obj.arrow).app V)) :
    IsColimit (cardinalGeneratedSubobjectCocone M κ) := by
  have hfil : IsFiltered (SmallModel (CardinalGeneratedSubobject M κ)) :=
    IsFiltered.of_equivalence (equivSmallModel (CardinalGeneratedSubobject M κ))
  refine IsColimit.ofWhiskerEquivalence (smallIndexEquiv M κ) (isColimit_of_forget _ ?_)
  let Dm := smallMonoOverDiagram M κ ⋙ MonoOver.forget M.module ⋙ Over.forget M.module
  let cm : Cocone Dm := (QuasicoherentModule.forget G).mapCocone
    ((cardinalGeneratedSubobjectCocone M κ).whisker (smallIndexEquiv M κ).functor)
  let f : colimit Dm ⟶ M.module := colimit.desc Dm cm
  have hf : ∀ j, colimit.ι Dm j ≫ f = ((smallMonoOverDiagram M κ).obj j).obj.hom :=
    fun j ↦ colimit.ι_desc cm j
  have hmono : Mono f :=
    IsGrothendieckAbelian.mono_of_isColimit_monoOver (smallMonoOverDiagram M κ)
      (colimit.isColimit Dm) f hf
  have hiso : IsIso f := by
    refine @CardinalGeneration.isIso_of_mono_of_locallySurjective _ _ _ f hmono ?_
    intro O z x hx
    obtain ⟨V, hVO, hxV, Q, y, hy⟩ := h O z x hx
    refine ⟨V, hVO, hxV, ?_⟩
    let j := (equivSmallModel (CardinalGeneratedSubobject M κ)).functor.obj Q
    let α : Q ⟶ (smallIndexEquiv M κ).functor.obj j :=
      (equivSmallModel (CardinalGeneratedSubobject M κ)).unitIso.hom.app Q
    let g : (QuasicoherentModule.forget G).obj (Subobject.underlying.obj Q.obj) ⟶ Dm.obj j :=
      (QuasicoherentModule.forget G).map
        (Subobject.underlying.map ((cardinalGeneratedSubobjectProperty M κ).ι.map α))
    have e1 : (g ≫ colimit.ι Dm j) ≫ f =
        (QuasicoherentModule.forget G).map Q.obj.arrow := by
      rw [Category.assoc, hf j]
      change (QuasicoherentModule.forget G).map
          (Subobject.underlying.map ((cardinalGeneratedSubobjectProperty M κ).ι.map α)) ≫
          (QuasicoherentModule.forget G).map
            ((smallIndexEquiv M κ).functor.obj j).obj.arrow =
        (QuasicoherentModule.forget G).map Q.obj.arrow
      rw [← Functor.map_comp]
      exact congrArg (QuasicoherentModule.forget G).map (Subobject.underlying_arrow _)
    refine ⟨(g ≫ colimit.ι Dm j).app V y, ?_⟩
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using (congrArg
      (fun m : (QuasicoherentModule.forget G).obj (Subobject.underlying.obj Q.obj) ⟶ M.module ↦
        m.app V y) e1).trans hy
  exact IsColimit.ofIsoColimit (colimit.isColimit Dm)
    (Cocone.ext (@asIso _ _ _ _ f hiso) fun j ↦ colimit.ι_desc cm j)

/-- **Stacks 077U, the colimit assertion.**  Every quasi-coherent module on a groupoid scheme with
flat source and target is the colimit of the canonical diagram of its quasi-coherent submodules
whose underlying module is generated by at most `cardinalBound G` local sections. -/
@[stacks 077U "colimit"]
def isColimit_cardinalGeneratedSubobjectCocone (M : QuasicoherentModule G) :
    IsColimit (cardinalGeneratedSubobjectCocone M (cardinalBound G)) := by
  refine isColimit_cocone_of_locally_mem M (cardinalBound G) fun O z x hx ↦ ?_
  obtain ⟨Pq, jj, hjmono, hgen, y, hy⟩ :=
    exists_invariantObject_of_section M (aleph0_le_cardinalBound G)
      (mk_affineOpens_objects_le_cardinalBound G) (mk_affineOpens_arrows_le_cardinalBound G) O z
  refine ⟨O, le_rfl, hx, ?_⟩
  refine ⟨⟨@Subobject.mk _ _ _ _ jj hjmono, ?_⟩, ?_⟩
  · exact CardinalGeneration.isCardinalGenerated_of_iso (cardinalBound G)
      ((QuasicoherentModule.forget G).mapIso
        (@Subobject.underlyingIso _ _ _ _ jj hjmono).symm) hgen
  · refine ⟨((QuasicoherentModule.forget G).map
      (@Subobject.underlyingIso _ _ _ _ jj hjmono).inv).app O y, ?_⟩
    have e2 : (QuasicoherentModule.forget G).map
          (@Subobject.underlyingIso _ _ _ _ jj hjmono).inv ≫
        (QuasicoherentModule.forget G).map (@Subobject.mk _ _ _ _ jj hjmono).arrow =
        (QuasicoherentModule.forget G).map jj := by
      rw [← Functor.map_comp, Subobject.underlyingIso_arrow]
    rw [Stacks.AlgebraicGeometry.GabberColimit.res_self]
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using
      (congrArg (fun m : Pq.module ⟶ M.module ↦ m.app O y) e2).trans hy

end Flat

end Stacks.AlgebraicGeometry.GroupoidCardinalGeneration

end
