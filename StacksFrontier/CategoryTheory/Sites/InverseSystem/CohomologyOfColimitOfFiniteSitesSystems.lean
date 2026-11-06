module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
import all StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ColimitsOfSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.InjectiveSystemsOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Cohomology of a colimit of finite sites: systems of sheaves and their colimit presentations

This module carries the declarations that extend
`StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites`,
which is the base text, unchanged.
-/

@[expose] public section

universe uu1 uu2 uu3 ww

open CategoryTheory CategoryTheory.Sites.InverseSystem Opposite

namespace StacksWeakAux

end StacksWeakAux

end

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w t z

namespace InverseSystemOfFiniteSites

section CompIsoSections



end CompIsoSections

/-- **A system of sheaves of SETS on an inverse system of sites**, with the inverse-image
transition maps.

The transition maps are carried in the presheaf form `F_i ⟶ u_a^{-1} F_j` with the cocycle law
written out on sections, rather than as morphisms of sheaves between pullbacks as
`AbelianSheafSystem` carries them. That is the form in which the colimit statements for sheaves of
sets consume them -- the `ψ` and `hψ` of
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit` and of
`InverseSystemOfFiniteSites.sections_colimit_pullback_of_colimit` -- so the bundle is a packaging
of those arguments and nothing more.

Why bundle them at all, when the set-valued API has always taken them unbundled. A statement about
a CONCRETE system cannot afford to spell them out: written at a system which is a projection of a
large structure literal, the unbundled hypotheses exceed the heartbeat budget in the signature,
before any proof runs, because each of some thirty occurrences of `D.I`, `D.C i`, `D.u a` and
`D.J i` forces the elaborator through that definition again. `AbelianSheafSystem` exists for the
same reason and predates this: it is what lets the signature of an abelian consumer mention its
system four times instead of thirty. This is its set-valued counterpart, which the development had
not needed until a geometric instantiation of the degree-zero statement wanted one. -/
structure SheafSystem (D : InverseSystemOfFiniteSites.{v, u, w}) where
  /-- The sheaf of sets at an index. -/
  obj : ∀ i, Sheaf (D.J i) (Type w)
  /-- The inverse-image transition morphism, in presheaf form. -/
  map : ∀ {i j : D.I} (a : j ⟶ i), (obj i).obj ⟶ (D.u a).op ⋙ (obj j).obj
  /-- The cocycle law: transition along a composite is the composite of the transitions, up to the
  identification of `u_{b ≫ a}` with `u_b ⋙ u_a` recorded by the system. -/
  map_comp : ∀ {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (V : D.C i)
    (x : (obj i).obj.obj (Opposite.op V)),
    (map (b ≫ a)).app (Opposite.op V) x =
      (obj k).obj.map (eqToHom (congrArg Opposite.op
          (Functor.congr_obj (D.comp b a) V).symm))
        ((map b).app (Opposite.op ((D.u a).obj V)) ((map a).app (Opposite.op V) x))

/-- **`𝒢` with the family `ι` is `colim f_i^{-1} F_i`**, for sheaves of sets: the family is
compatible with the transitions, and every compatible family of maps to a sheaf `H` on the colimit
site factors uniquely through `ι`.

This bundles the two hypotheses a colimit presentation is given by in the set-valued statements --
the `hι` and `hG` of
`Stacks.WeakSites.ColimitGlobalSections.objectSections_jointlySurjective_and_separated` -- and is
the set-valued counterpart of `InverseSystemOfFiniteSites.IsColimitPresentation`, whose docstring
records that the universal property it states for abelian sheaves is the one by which the case
`p = 0` of Stacks 09YN presents the same colimit for sheaves of sets. -/
def SheafSystem.IsColimitPresentation {D : InverseSystemOfFiniteSites.{v, u, w}}
    (F : SheafSystem.{v, u, w} D) {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j) (K : Precoverage C)
    (G : Sheaf K.toGrothendieck (Type w))
    (ι : ∀ i, (F.obj i).obj ⟶ (uC i).op ⋙ G.obj) : Prop :=
  (∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : (F.obj i).obj.obj (Opposite.op V)),
      (ι i).app (Opposite.op V) x =
        G.obj.map (eqToHom (congrArg Opposite.op (Functor.congr_obj (hu a) V)))
          ((ι j).app (Opposite.op ((D.u a).obj V)) ((F.map a).app (Opposite.op V) x))) ∧
    ∀ (H : Sheaf K.toGrothendieck (Type w)) (g : ∀ i, (F.obj i).obj ⟶ (uC i).op ⋙ H.obj),
      (∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : (F.obj i).obj.obj (Opposite.op V)),
          (g i).app (Opposite.op V) x =
            H.obj.map (eqToHom (congrArg Opposite.op (Functor.congr_obj (hu a) V)))
              ((g j).app (Opposite.op ((D.u a).obj V))
                ((F.map a).app (Opposite.op V) x))) →
        ∃! h : G ⟶ H, ∀ (i : D.I) (V : D.C i) (x : (F.obj i).obj.obj (Opposite.op V)),
          (g i).app (Opposite.op V) x =
            h.hom.app (Opposite.op ((uC i).obj V)) ((ι i).app (Opposite.op V) x)

namespace AbelianSheafSystem

attribute [local implicit_reducible] incomingFactor injectiveEnvelope

end AbelianSheafSystem

end InverseSystemOfFiniteSites

end

namespace CategoryTheory.Sites.InverseSystem

section

universe u₁ u₂ w
open CategoryTheory Opposite

namespace Stacks.WeakSites.ColimitSheafSections

@[expose] public section

section

variable {C : Type w} [SmallCategory C] (D : InverseSystemOfFiniteSites.{u₁, u₂, w})
  (u : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
  (hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (u i).obj Y = X)
  (hhom :
    ∀ (i : D.I) (X Y : D.C i) (f : (u i).obj X ⟶ (u i).obj Y),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj X ⟶ (D.u a).obj Y),
        (u j).map g =
          eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Y).symm)
  (hhom_inj :
    ∀ (i : D.I) (X Y : D.C i) (g₁ g₂ : X ⟶ Y),
      (u i).map g₁ = (u i).map g₂ → ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK :
    ∀ (X : C) (R : Presieve X),
      R ∈ K X ↔
        ∃ (i : D.I) (Y : D.C i) (h : (u i).obj Y = X) (S : Presieve Y),
          S ∈ (D.J i).toPrecoverage Y ∧ S ∈ Precoverage.finite (D.C i) Y ∧ R = h ▸ S.map (u i))
  (F : ∀ i, Sheaf (D.J i) (Type w))
  (ψ : ∀ {i j : D.I} (a : j ⟶ i), (F i).obj ⟶ (D.u a).op ⋙ (F j).obj)
  (hψ :
    ∀ {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (V : D.C i) (x : (F i).obj.obj (op V)),
      (ψ (b ≫ a)).app (op V) x =
        (F k).obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp b a) V).symm))
          ((ψ b).app (op ((D.u a).obj V)) ((ψ a).app (op V) x)))
  (G : Sheaf K.toGrothendieck (Type w)) (ι : ∀ i, (F i).obj ⟶ (u i).op ⋙ G.obj)
  (hι :
    ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : (F i).obj.obj (op V)),
      (ι i).app (op V) x =
        G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V)))
          ((ι j).app (op ((D.u a).obj V)) ((ψ a).app (op V) x)))
  (hG :
    ∀ (H : Sheaf K.toGrothendieck (Type w)) (g : ∀ i, (F i).obj ⟶ (u i).op ⋙ H.obj),
      (∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : (F i).obj.obj (op V)),
          (g i).app (op V) x =
            H.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V)))
              ((g j).app (op ((D.u a).obj V)) ((ψ a).app (op V) x))) →
        ∃! h : G ⟶ H,
          ∀ (i : D.I) (V : D.C i) (x : (F i).obj.obj (op V)),
            (g i).app (op V) x = h.hom.app (op ((u i).obj V)) ((ι i).app (op V) x))

end

end

end Stacks.WeakSites.ColimitSheafSections

@[expose] public section

end

end

end CategoryTheory.Sites.InverseSystem

namespace CategoryTheory.Sites.InverseSystem

section

universe u₁ u₂ w v₃ u₃ u₄ v₄
open CategoryTheory Opposite
open CategoryTheory Limits Opposite

namespace Stacks.WeakSites.ColimitMorphismOfSites

@[expose] public section

section Factorization

variable {X Y Z : Type w} [SmallCategory X] [SmallCategory Y] [SmallCategory Z]

end Factorization

section FactorizationComp

variable {X Y Z T : Type w} [SmallCategory X] [SmallCategory Y] [SmallCategory Z] [SmallCategory T]

end FactorizationComp

section FilteredColimitExactness

end FilteredColimitExactness

section Evaluation

end Evaluation

section

variable {C : Type w} [SmallCategory C] (D : InverseSystemOfFiniteSites.{u₁, u₂, w})
  (u : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
  (hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (u i).obj Y = X)
  (hhom :
    ∀ (i : D.I) (X Y : D.C i) (f : (u i).obj X ⟶ (u i).obj Y),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj X ⟶ (D.u a).obj Y),
        (u j).map g =
          eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Y).symm)
  (hhom_inj :
    ∀ (i : D.I) (X Y : D.C i) (g₁ g₂ : X ⟶ Y),
      (u i).map g₁ = (u i).map g₂ → ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK :
    ∀ (X : C) (R : Presieve X),
      R ∈ K X ↔
        ∃ (i : D.I) (Y : D.C i) (h : (u i).obj Y = X) (S : Presieve Y),
          S ∈ (D.J i).toPrecoverage Y ∧ S ∈ Precoverage.finite (D.C i) Y ∧ R = h ▸ S.map (u i))

end

end


end Stacks.WeakSites.ColimitMorphismOfSites

@[expose] public section

end

end

end CategoryTheory.Sites.InverseSystem

namespace CategoryTheory.Sites.InverseSystem

section

universe u₁ u₂ w
open CategoryTheory Opposite

namespace Stacks.WeakSites.ColimitPresheafDescent

@[expose] public section

section GeneralTarget

variable {C : Type w} [SmallCategory C] (D : InverseSystemOfFiniteSites.{u₁, u₂, w})
  (u : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
  {A : Type*} [Category* A] {P Q : Cᵒᵖ ⥤ A}
  (g : ∀ i, (u i).op ⋙ P ⟶ (u i).op ⋙ Q)
  (hg :
    ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i),
      (g i).app (op V) =
        P.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V).symm)) ≫
          (g j).app (op ((D.u a).obj V)) ≫
            Q.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V))))
  (hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (u i).obj Y = X)
  (hhom :
    ∀ (i : D.I) (X Y : D.C i) (f : (u i).obj X ⟶ (u i).obj Y),
      ∃ (j : D.I) (a : j ⟶ i) (φ : (D.u a).obj X ⟶ (D.u a).obj Y),
        (u j).map φ =
          eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Y).symm)

namespace General

/-- The map on sections over an object `X` of `C` induced by a family `g` of maps on sections at
the levels, through a presentation `u_i(V) = X` of `X` at the level `i`.

The target category is arbitrary, so this is a *morphism* `P(X) ⟶ Q(X)` — a composite of the
transport of `P` along the presentation, the map `g i` at `V`, and the transport of `Q` back. The
`Type`-valued development below is this one at `A := Type w`. -/
private def appOfObjEq {i : D.I} {V : D.C i} {X : C} (p : (u i).obj V = X) :
    P.obj (op X) ⟶ Q.obj (op X) :=
  P.map (eqToHom (congrArg op p.symm)) ≫ (g i).app (op V) ≫ Q.map (eqToHom (congrArg op p))

/-- Through the tautological presentation of `u_i(V)`, the induced map is `g i` at `V`. -/
private lemma appOfObjEq_rfl {i : D.I} (V : D.C i) :
    appOfObjEq D u g (rfl : (u i).obj V = (u i).obj V) = (g i).app (op V) := by
  simp [appOfObjEq]

include hg in
/-- The map induced by a presentation of `X` at the level `i` is also induced by the presentation
of `X` at any lower level, got by composing with the transition functor. -/
private lemma appOfObjEq_comp {i j : D.I} (a : j ⟶ i) {V : D.C i} {X : C}
    (p : (u i).obj V = X) :
    appOfObjEq D u g p = appOfObjEq D u g ((Functor.congr_obj (hu a) V).trans p) := by
  subst p
  rw [appOfObjEq_rfl]
  exact hg a V

/-- **The induced maps are compatible with restriction along a morphism of `C` which is the image
of a morphism at a level.** This is the naturality of the single map `g m`, read through
presentations of the source and the target. -/
private lemma appOfObjEq_map_of_hom {m : D.I} {B₁ B₂ : D.C m} {X Y : C} (pA : (u m).obj B₁ = X)
    (pB : (u m).obj B₂ = Y) (f : X ⟶ Y) (φ : B₁ ⟶ B₂)
    (hφ : (u m).map φ = eqToHom pA ≫ f ≫ eqToHom pB.symm) :
    P.map f.op ≫ appOfObjEq D u g pA = appOfObjEq D u g pB ≫ Q.map f.op := by
  subst pA
  subst pB
  rw [appOfObjEq_rfl, appOfObjEq_rfl]
  obtain rfl : f = (u m).map φ := by rw [hφ]; simp
  exact (g m).naturality φ.op

include hu hg hhom in
/-- **The induced maps are compatible with restriction along every morphism of `C`.** This is the
whole content of the descent: the presentations of `X` and of `Y` are pushed down to a common
level, and then by `hhom` to a level at which `f` is the image of a morphism `φ`, where the claim
is the naturality of the single map `g` at that level. -/
private lemma appOfObjEq_map {i j : D.I} {V : D.C i} {W : D.C j} {X Y : C}
    (p : (u i).obj V = X) (p' : (u j).obj W = Y) (f : X ⟶ Y) :
    P.map f.op ≫ appOfObjEq D u g p = appOfObjEq D u g p' ≫ Q.map f.op := by
  obtain ⟨l, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs (C := D.I) i j
  obtain ⟨m, c, φ, hφ⟩ :=
    hhom l ((D.u a).obj V) ((D.u b).obj W)
      (eqToHom ((Functor.congr_obj (hu a) V).trans p) ≫
        f ≫ eqToHom ((Functor.congr_obj (hu b) W).trans p').symm)
  rw [appOfObjEq_comp D u hu g hg a p, appOfObjEq_comp D u hu g hg b p',
    appOfObjEq_comp D u hu g hg c _, appOfObjEq_comp D u hu g hg c _]
  refine appOfObjEq_map_of_hom D u g _ _ f φ ?_
  rw [hφ]
  simp

include hu hg hhom in
/-- **The induced map does not depend on the presentation**: `appOfObjEq_map` for the identity of
`X`. -/
private lemma appOfObjEq_congr {i j : D.I} {V : D.C i} {W : D.C j} {X : C}
    (p : (u i).obj V = X) (p' : (u j).obj W = X) :
    appOfObjEq D u g p = appOfObjEq D u g p' := by
  simpa using appOfObjEq_map D u hu g hg hhom p p' (𝟙 X)

include hu hg hhom in
/-- The morphism of presheaves on `C` descending the family `g`, through a choice for every object
`X` of `C` of a presentation `u_{lv X}(ob X) = X` of `X` at the level `lv X`. -/
private def descend (lv : C → D.I) (ob : ∀ X : C, D.C (lv X))
    (hob : ∀ X : C, (u (lv X)).obj (ob X) = X) : P ⟶ Q where
  app B := appOfObjEq D u g (hob B.unop)
  naturality _ _ n := appOfObjEq_map D u hu g hg hhom (hob _) (hob _) n.unop

include hu hg hhom in
/-- **`descend` restricts to `g i` at every level**: whichever presentation was chosen for
`u_i(V)`, the induced map there is `g i` at `V`. -/
private lemma descend_app_obj (lv : C → D.I) (ob : ∀ X : C, D.C (lv X))
    (hob : ∀ X : C, (u (lv X)).obj (ob X) = X) (i : D.I) (V : D.C i) :
    (descend D u hu g hg hhom lv ob hob).app (op ((u i).obj V)) = (g i).app (op V) :=
  (appOfObjEq_congr D u hu g hg hhom (hob ((u i).obj V)) rfl).trans (appOfObjEq_rfl D u g V)

include hu hg hobj hhom in
/-- **The morphism of presheaves on `C` descending the family `g`**, through the presentation of
every object of `C` at some level that `hobj` supplies. The target category is arbitrary. -/
@[no_expose]
public noncomputable def natTrans : P ⟶ Q :=
  descend D u hu g hg hhom (fun X => (hobj X).choose) (fun X => (hobj X).choose_spec.choose)
    fun X => (hobj X).choose_spec.choose_spec

include hu hg hobj hhom in
/-- **`General.natTrans` restricts to `g i` at every level.** This is the existence half of the
universal property. -/
public lemma natTrans_app_obj (i : D.I) (V : D.C i) :
    (natTrans D u hu g hg hobj hhom).app (op ((u i).obj V)) = (g i).app (op V) :=
  descend_app_obj D u hu g hg hhom _ _ _ i V

include hobj in
/-- **A map of presheaves on `C` is determined by its restrictions to the levels**: the uniqueness
half of the universal property, needing only that every object of `C` comes from a level. -/
public lemma natTrans_ext {y z : P ⟶ Q}
    (h : ∀ (i : D.I) (V : D.C i), y.app (op ((u i).obj V)) = z.app (op ((u i).obj V))) :
    y = z := by
  refine NatTrans.ext (funext fun B => ?_)
  obtain ⟨X⟩ := B
  obtain ⟨i, V, rfl⟩ := hobj X
  exact h i V

include hu hg hobj hhom in
/-- **`General.natTrans` is the only map of presheaves on `C` restricting to `g i` at every
level.** This is the uniqueness half of the universal property. -/
public lemma eq_natTrans (y : P ⟶ Q)
    (hy : ∀ (i : D.I) (V : D.C i), (g i).app (op V) = y.app (op ((u i).obj V))) :
    y = natTrans D u hu g hg hobj hhom :=
  natTrans_ext D u hobj fun i V =>
    (hy i V).symm.trans (natTrans_app_obj D u hu g hg hobj hhom i V).symm

end General

end GeneralTarget

section Descent

variable {C : Type w} [SmallCategory C] (D : InverseSystemOfFiniteSites.{u₁, u₂, w})
  (u : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j) {P Q : Cᵒᵖ ⥤ Type w}
  (g : ∀ i, (u i).op ⋙ P ⟶ (u i).op ⋙ Q)
  (hg :
    ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : P.obj (op ((u i).obj V))),
      (g i).app (op V) x =
        Q.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V)))
          ((g j).app (op ((D.u a).obj V))
            (P.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V).symm)) x)))
  (hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (u i).obj Y = X)
  (hhom :
    ∀ (i : D.I) (X Y : D.C i) (f : (u i).obj X ⟶ (u i).obj Y),
      ∃ (j : D.I) (a : j ⟶ i) (φ : (D.u a).obj X ⟶ (D.u a).obj Y),
        (u j).map φ =
          eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Y).symm)

include hg in
/-- For a `Type`-valued target the compatibility of `g` read on elements is its morphism form,
which is what `General` asks for. -/
public lemma hg_hom {i j : D.I} (a : j ⟶ i) (V : D.C i) :
    (g i).app (op V) =
      P.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V).symm)) ≫
        (g j).app (op ((D.u a).obj V)) ≫
          Q.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V))) :=
  ConcreteCategory.ext_apply fun x => by simpa using hg a V x

end Descent

end

end Stacks.WeakSites.ColimitPresheafDescent

@[expose] public section

namespace InverseSystemOfFiniteSites

end InverseSystemOfFiniteSites

end

end

end CategoryTheory.Sites.InverseSystem

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance_reducible] HomologicalComplex.single HomologicalComplex.homologyFunctor
  CategoryTheory.Functor.sheafPushforwardContinuous

universe v u w t s

namespace Stacks.WeakSites.ColimitSiteCohomology



section SystemCokernel

open InverseSystemOfFiniteSites

attribute [local instance_reducible] systemOfPushforwardMaps systemCokernel

attribute [local instance_reducible] systemSyzygy

end SystemCokernel

attribute [local instance_reducible] systemOfPushforwardMaps systemCokernel systemSyzygy

section AbelianRestriction

end AbelianRestriction

section SectionsDiagram










end SectionsDiagram

section TotalSite







end TotalSite

section FiniteCoverings

universe z

end FiniteCoverings

section KanSheaf
variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))

variable (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)

include hobj hhom hhom_inj hK in
attribute [local instance_reducible] systemColimitSheaf


end KanSheaf

section SystemColimits

attribute [local instance_reducible] systemColimitSheaf

variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))

section SectionsFac

attribute [local implicit_reducible] sectionsDiagram sectionsCocone


end SectionsFac

end SystemColimits

section CanonicalDiagram

variable (D : InverseSystemOfFiniteSites.{v, u, w})
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
  [htrans : ∀ {j k : D.I} (a : j ⟶ k),
    (InverseSystemOfFiniteSites.abelianSheafPushforward.{v, u, w, t} D a).PreservesInjectiveObjects]

section

attribute [local instance_reducible] sectionsDiagram canonicalCohomologyDiagram


end

variable {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (K : Precoverage C)
  [hcont : ∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck]
  [hleg : ∀ j, letI := hcont j
    ((uC j).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J j) K.toGrothendieck).PreservesInjectiveObjects]
  (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t}))
  (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
  (hι : IsCompatible D uC hu F 𝒢.obj ι)

end CanonicalDiagram

section ExactColimits

end ExactColimits

section CechColimits

end CechColimits

section ColimitPullbacks
variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)

end ColimitPullbacks

section CoveringProducts

attribute [local implicit_reducible] CategoryTheory.extendFan

end CoveringProducts

section CechMap

universe v' u' a b
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) {U : C} (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    HasProduct (fun a ↦ Over.mk ((E.map F).f (i a)))]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.f (i a)))) (Over.post F)]

attribute [local instance_reducible] CategoryTheory.PreZeroHypercover.map
attribute [local implicit_reducible] Stacks.CechSite.cechFormalCoproduct
  Stacks.CechSite.cechFormalCoproductMap

variable {A : Type a} [Category.{b} A] [HasProducts.{w} A] (P : Dᵒᵖ ⥤ A)

end CechMap

section ColimitAcyclicity

variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))

end ColimitAcyclicity

section ColimitAcyclicitySiteCoefficients

variable (D : InverseSystemOfFiniteSites.{v, u, max u v w}) {C : Type (max u v w)}
  [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))


end ColimitAcyclicitySiteCoefficients

section Leray

variable {𝒜 : Type*} {ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory 𝒜] [HasDerivedCategory ℬ] [EnoughInjectives 𝒜]
  (Γ : 𝒜 ⥤ ℬ) [Γ.Additive]

variable [PreservesFiniteLimits Γ]

end Leray

section ExactColimitHomology

variable {J : Type*} [Category* J] {A : Type*} [Category* A] [Abelian A]
  [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]

end ExactColimitHomology

section ComparisonMap

variable {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] {P : 𝒞}

end ComparisonMap

section MonoCokernelComplex

variable {A : Type*} [Category* A] [Abelian A] (Z I : ℕ → A)
  (ι : ∀ n, Z n ⟶ I n) (π : ∀ n, I n ⟶ Z (n + 1))
  (hmono : ∀ n, Mono (ι n)) (hepi : ∀ n, Epi (π n))
  (hzero : ∀ n, ι n ≫ π n = 0)
  (hex : ∀ n, (ShortComplex.mk (ι n) (π n) (hzero n)).Exact)
  (hdd : ∀ n, (π n ≫ ι (n + 1)) ≫ (π (n + 1) ≫ ι (n + 1 + 1)) = 0)

end MonoCokernelComplex

section ColimitResolution

variable (D : InverseSystemOfFiniteSites.{v, u, max u v w}) {C : Type (max u v w)}
  [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} D)

variable [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck]


variable (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w}))
  (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)

variable (e : systemColimitSheaf.{v, u, max u v w, max u v w}
    D uC hu hobj hhom hhom_inj K hK F ≅ 𝒢)

variable (he : ∀ j, systemKanUnit.{v, u, max u v w, max u v w} D uC hu F j ≫
    Functor.whiskerLeft (uC j).op e.hom.hom = ι j)
  (i : D.I) (X : D.C i)


attribute [local instance_reducible] colimitResolutionComplex systemColimitSheaf

end ColimitResolution

section Tag09YP

variable (D : InverseSystemOfFiniteSites.{v, u, max u v w}) {C : Type (max u v w)}
  [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} D)
  (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w}))
  (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
  (hcolim : IsColimitPresentation.{v, u, max u v w, max u v w} D uC hu K F 𝒢 ι)
  (i : D.I) (X : D.C i) (p : ℕ)

end Tag09YP

section RestrictionSystem

open InverseSystemOfFiniteSites

namespace RestrictionSystem

/-- Three transports along equalities of objects compose to one. The equalities are on
variables, so they can be substituted away; the chains of transports that the comparison
isomorphisms of direct images produce are then closed by `exact`, whose unifier sees through the
defeq-but-not-syntactic descriptions of the intermediate objects that block `rw`. -/
theorem map_eqToHom_comp₃ {B : Type*} [Category* B] {A : Type*} [Category* A] (P : B ⥤ A)
    {X Y Z W : B} (p : X = Y) (q : Y = Z) (s : Z = W) :
    P.map (eqToHom p) ≫ P.map (eqToHom q) ≫ P.map (eqToHom s) =
      P.map (eqToHom (p.trans (q.trans s))) := by
  subst p
  subst q
  subst s
  simp

/-- The same device one level up, at natural transformations: the canonical transport across an
identification `T ⋙ Q = P` of functors, with the whiskered identity of `Q` between its two
halves, is the identity of `P`.

The equality is again on a variable, so `subst` removes it, and the lemma is applied with `exact`.
That is what makes it usable: the two transports and the whiskered identity meet at a functor that
the transport describes one way and the whiskering another, definitionally equal but not
syntactically equal, so `Functor.whiskerLeft_app`, `NatTrans.comp_app` and `eqToHom_trans` all
fail to fire and no `simp` set closes the goal. -/
theorem eqToHom_symm_comp_whiskerLeft_id_comp_eqToHom {E : Type*} [Category* E] {B : Type*}
    [Category* B] {A : Type*} [Category* A] (T : E ⥤ B) (Q : B ⥤ A) {P : E ⥤ A}
    (h : T ⋙ Q = P) :
    eqToHom h.symm ≫ Functor.whiskerLeft T (𝟙 Q) ≫ eqToHom h = 𝟙 P := by
  subst h
  simp

/-- The same device for a general whiskered transformation rather than an identity: the sections
of a transport–whiskering–transport composite, with the two identifications on variables so that
`subst` removes them. Applied with `exact`, for the same reason. -/
theorem comp_app_of_eqToHom {E : Type*} [Category* E] {B : Type*} [Category* B] {A : Type*}
    [Category* A] (T : E ⥤ B) {P Q : B ⥤ A} {P' Q' : E ⥤ A} (hP : T ⋙ P = P')
    (hQ : T ⋙ Q = Q') (α : P ⟶ Q) (X : E) :
    (eqToHom hP.symm ≫ Functor.whiskerLeft T α ≫ eqToHom hQ).app X =
      eqToHom (congrArg (fun F : E ⥤ A => F.obj X) hP.symm) ≫ α.app (T.obj X) ≫
        eqToHom (congrArg (fun F : E ⥤ A => F.obj X) hQ) := by
  subst hP
  subst hQ
  simp

variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (K : Precoverage C) [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
  (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t}))

/-- Restriction of a sheaf on the colimit site to the site of a level. -/
noncomputable abbrev restrict (i : D.I) :
    Sheaf K.toGrothendieck (Ab.{max u v w t}) ⥤ Sheaf (D.J i) (Ab.{max u v w t}) :=
  (uC i).sheafPushforwardContinuous (Ab.{max u v w t}) (D.J i) K.toGrothendieck

/-- The direct-image form of the transition of the canonical system: the comparison of the
restrictions to two levels along the equality `D.u a ⋙ uC i = uC j`. -/
noncomputable def restrictComp {i j : D.I} (a : i ⟶ j) :
    restrict.{v, u, w, t} D uC K i ⋙ abelianSheafPushforward.{v, u, w, t} D a ≅
      restrict.{v, u, w, t} D uC K j :=
  letI := D.continuous a
  Functor.sheafPushforwardContinuousComp' (eqToIso (hu a)) (Ab.{max u v w t})
    (D.J j) (D.J i) K.toGrothendieck

/-- Sections of the comparison: it is the restriction map of `𝒢` along the equality `hu a`. -/
theorem restrictComp_inv_app_app {i j : D.I} (a : i ⟶ j) (V : D.C j) :
    (((restrictComp.{v, u, w, t} D uC hu K a).inv.app 𝒢).hom.app (op V)) =
      𝒢.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a).symm V))) := by
  let := D.continuous a
  exact sheafPushforwardContinuousComp'_inv_app_app.{w, max u v w t} (hu a)
    (D.J j) (D.J i) K.toGrothendieck 𝒢 V

/-- **The comparison is the canonical transport.** On underlying presheaves the comparison of the
restrictions to two levels is nothing but the transport across
`Stacks.WeakSites.ColimitSiteCohomology.restrict_eq`, the identification of
`(D.u a)^{op} ⋙ uₖ^{op} ⋙ 𝒢` with `uⱼ^{op} ⋙ 𝒢` that `hu a` gives.

This is the form in which the compatibility of the identity legs is proved: it replaces a
transport built out of `Functor.sheafPushforwardContinuousComp'` by a bare `eqToHom`, after which
the coherence is `eqToHom` algebra. -/
theorem restrictComp_inv_hom_eq_eqToHom {j k : D.I} (a : k ⟶ j) :
    ((restrictComp.{v, u, w, t} D uC hu K a).inv.app 𝒢).hom =
      eqToHom (restrict_eq.{v, u, w, t} D uC hu a 𝒢.obj).symm := by
  refine NatTrans.ext (funext fun U => ?_)
  obtain ⟨V⟩ := U
  rw [restrictComp_inv_app_app, eqToHom_app, eqToHom_map]

/-- Sections of the direct image of a morphism of sheaves. -/
theorem push_map_hom_app {i j : D.I} (b : i ⟶ j) {X Y : Sheaf (D.J i) (Ab.{max u v w t})}
    (φ : X ⟶ Y) (V : D.C j) :
    ((abelianSheafPushforward.{v, u, w, t} D b).map φ).hom.app (op V) =
      φ.hom.app (op ((D.u b).obj V)) := rfl

/-- Restriction acts on sections by `𝒢`'s own restriction along `uC i`. -/
theorem restrict_obj_obj_map (i : D.I) {U V : (D.C i)ᵒᵖ} (f : U ⟶ V) :
    ((restrict.{v, u, w, t} D uC K i).obj 𝒢).obj.map f = 𝒢.obj.map ((uC i).op.map f) := rfl

/-- `eqToHom` passes through the opposite of a level functor. -/
theorem uCop_map_eqToHom (i : D.I) {U V : (D.C i)ᵒᵖ} (h : U = V) :
    (uC i).op.map (eqToHom h) = eqToHom (congrArg (uC i).op.obj h) :=
  eqToHom_map _ h

/-- **The cocycle identity on the direct-image side**: the comparison for a composite transition
is the composite of the two comparisons, read through the comparison of the direct images. -/
theorem restrictComp_cocycle {i j k : D.I} (a : i ⟶ j) (b : j ⟶ k) :
    (restrictComp.{v, u, w, t} D uC hu K (a ≫ b)).inv.app 𝒢 =
      (restrictComp.{v, u, w, t} D uC hu K b).inv.app 𝒢 ≫
        (abelianSheafPushforward.{v, u, w, t} D b).map
            ((restrictComp.{v, u, w, t} D uC hu K a).inv.app 𝒢) ≫
          (abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app
            ((restrict.{v, u, w, t} D uC K i).obj 𝒢) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  obtain ⟨V⟩ := U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    restrictComp_inv_app_app, pushforwardCompIso_hom_app_app, push_map_hom_app,
    restrict_obj_obj_map, uCop_map_eqToHom]
  exact (map_eqToHom_comp₃ 𝒢.obj _ _ _).symm

/-- **The unit law on the direct-image side**: the comparison for an identity transition is the
comparison of the direct image along an identity with the identity functor. -/
theorem restrictComp_id (i : D.I) :
    (restrictComp.{v, u, w, t} D uC hu K (𝟙 i)).inv.app 𝒢 =
      (abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app
        ((restrict.{v, u, w, t} D uC K i).obj 𝒢) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  obtain ⟨V⟩ := U
  simp only [restrictComp_inv_app_app, pushforwardIdIso_hom_app_app, restrict_obj_obj_map,
    uCop_map_eqToHom]
  rfl

/-- The inverse-image form of the transition of the canonical system: the transpose of
`RestrictionSystem.restrictComp` across the inverse-image/direct-image adjunction. -/
noncomputable def map {i j : D.I} (a : i ⟶ j) :
    (abelianSheafPullback.{v, u, w, t} D a).obj ((restrict.{v, u, w, t} D uC K j).obj 𝒢) ⟶
      (restrict.{v, u, w, t} D uC K i).obj 𝒢 :=
  ((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _).symm
    ((restrictComp.{v, u, w, t} D uC hu K a).inv.app 𝒢)

/-- The transition transposes back to the comparison it was defined from. -/
theorem homEquiv_map {i j : D.I} (a : i ⟶ j) :
    (abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _ (map.{v, u, w, t} D uC hu K 𝒢 a) =
      (restrictComp.{v, u, w, t} D uC hu K a).inv.app 𝒢 :=
  Equiv.apply_symm_apply _ _

/-- The identity law of the canonical system, the field `AbelianSheafSystem.map_id`. -/
theorem map_id' (i : D.I) :
    (abelianSheafPullbackIdIso.{v, u, w, t} D i).inv.app
          ((restrict.{v, u, w, t} D uC K i).obj 𝒢) ≫
        map.{v, u, w, t} D uC hu K 𝒢 (𝟙 i) =
      𝟙 ((restrict.{v, u, w, t} D uC K i).obj 𝒢) := by
  have hunit : (abelianSheafAdjunction.{v, u, w, t} D (𝟙 i)).homEquiv
        ((restrict.{v, u, w, t} D uC K i).obj 𝒢) ((restrict.{v, u, w, t} D uC K i).obj 𝒢)
        ((abelianSheafPullbackIdIso.{v, u, w, t} D i).hom.app
          ((restrict.{v, u, w, t} D uC K i).obj 𝒢)) =
      (abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app
        ((restrict.{v, u, w, t} D uC K i).obj 𝒢) := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (abelianSheafAdjunction.{v, u, w, t} D (𝟙 i))
      (Adjunction.id.ofNatIsoRight (abelianSheafPushforwardIdIso.{v, u, w, t} D i))
      ((restrict.{v, u, w, t} D uC K i).obj 𝒢)
    simpa [abelianSheafPullbackIdIso, Adjunction.ofNatIsoRight] using h
  have key : map.{v, u, w, t} D uC hu K 𝒢 (𝟙 i) =
      (abelianSheafPullbackIdIso.{v, u, w, t} D i).hom.app
        ((restrict.{v, u, w, t} D uC K i).obj 𝒢) := by
    refine ((abelianSheafAdjunction.{v, u, w, t} D (𝟙 i)).homEquiv _ _).injective ?_
    rw [homEquiv_map, restrictComp_id, hunit]
  rw [key]
  exact Iso.inv_hom_id_app _ _

/-- The composition law of the canonical system, the field `AbelianSheafSystem.map_comp`. -/
theorem map_comp' {i j k : D.I} (a : i ⟶ j) (b : j ⟶ k) :
    (abelianSheafPullbackCompIso.{v, u, w, t} D a b).inv.app
          ((restrict.{v, u, w, t} D uC K k).obj 𝒢) ≫
        (abelianSheafPullback.{v, u, w, t} D a).map (map.{v, u, w, t} D uC hu K 𝒢 b) ≫
          map.{v, u, w, t} D uC hu K 𝒢 a =
      map.{v, u, w, t} D uC hu K 𝒢 (a ≫ b) := by
  have hmate := leftAdjointUniq_ofNatIsoRight_homEquiv_inv
    (abelianSheafAdjunction.{v, u, w, t} D b) (abelianSheafAdjunction.{v, u, w, t} D a)
    (abelianSheafAdjunction.{v, u, w, t} D (a ≫ b))
    (abelianSheafPushforwardCompIso.{v, u, w, t} D a b)
    (X := (restrict.{v, u, w, t} D uC K k).obj 𝒢)
    (Y := (restrict.{v, u, w, t} D uC K i).obj 𝒢)
    ((abelianSheafPullback.{v, u, w, t} D a).map (map.{v, u, w, t} D uC hu K 𝒢 b) ≫
      map.{v, u, w, t} D uC hu K 𝒢 a)
  have hf : ((abelianSheafAdjunction.{v, u, w, t} D b).comp
        (abelianSheafAdjunction.{v, u, w, t} D a)).homEquiv
      ((restrict.{v, u, w, t} D uC K k).obj 𝒢) ((restrict.{v, u, w, t} D uC K i).obj 𝒢)
      ((abelianSheafPullback.{v, u, w, t} D a).map (map.{v, u, w, t} D uC hu K 𝒢 b) ≫
        map.{v, u, w, t} D uC hu K 𝒢 a) =
      (restrictComp.{v, u, w, t} D uC hu K b).inv.app 𝒢 ≫
        (abelianSheafPushforward.{v, u, w, t} D b).map
          ((restrictComp.{v, u, w, t} D uC hu K a).inv.app 𝒢) := by
    refine (((abelianSheafAdjunction.{v, u, w, t} D b).comp
      (abelianSheafAdjunction.{v, u, w, t} D a)).homEquiv _ _).symm.injective ?_
    rw [Equiv.symm_apply_apply]
    simp only [Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
    rw [Adjunction.homEquiv_naturality_right_symm,
      Adjunction.homEquiv_naturality_left_symm]
    rfl
  have hpc : (((abelianSheafAdjunction.{v, u, w, t} D b).comp
        (abelianSheafAdjunction.{v, u, w, t} D a)).ofNatIsoRight
          (abelianSheafPushforwardCompIso.{v, u, w, t} D a b)).leftAdjointUniq
        (abelianSheafAdjunction.{v, u, w, t} D (a ≫ b)) =
      abelianSheafPullbackCompIso.{v, u, w, t} D a b := rfl
  rw [hpc] at hmate
  refine ((abelianSheafAdjunction.{v, u, w, t} D (a ≫ b)).homEquiv _ _).injective ?_
  rw [homEquiv_map, restrictComp_cocycle]
  conv_rhs => rw [← Category.assoc, ← hf, ← hmate, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

end RestrictionSystem

/-- **The canonical system of restrictions of a sheaf on the colimit site.** For a sheaf `𝒢` on
the colimit site whose restriction to every level is a sheaf there, the restrictions
`uᵢ^{op} ⋙ 𝒢` form a system of abelian sheaves on the inverse system of sites, with the
canonical identifications coming from `D.u a ⋙ uC i = uC j` as transitions.

This is the system that the source feeds to Stacks 09YP: the system of direct images of a sheaf
on the colimit site, Stacks 0EYN. That `𝒢` itself, with the identity legs, *presents*
`colim fᵢ⁻¹` of this system is a separate statement and is not proved here. -/
noncomputable def restrictionSystem (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w}
    [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (K : Precoverage C) [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
    (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t})) :
    InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D where
  obj i := (RestrictionSystem.restrict.{v, u, w, t} D uC K i).obj 𝒢
  map a := RestrictionSystem.map.{v, u, w, t} D uC hu K 𝒢 a
  map_id i := RestrictionSystem.map_id'.{v, u, w, t} D uC hu K 𝒢 i
  map_comp a b := RestrictionSystem.map_comp'.{v, u, w, t} D uC hu K 𝒢 a b

/-- The direct-image transition of the canonical system is the comparison it was built from. -/
theorem transition_restrictionSystem (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w}
    [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (K : Precoverage C) [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
    (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t})) {i j : D.I} (a : i ⟶ j) :
    transition.{v, u, w, t} D (restrictionSystem.{v, u, w, t} D uC hu K 𝒢) a =
      ((RestrictionSystem.restrictComp.{v, u, w, t} D uC hu K a).inv.app 𝒢).hom :=
  congrArg (fun φ => φ.hom) (RestrictionSystem.homEquiv_map.{v, u, w, t} D uC hu K 𝒢 a)

/-- **The identity legs of the canonical system are compatible with its transitions.** This is
the first of the two clauses of `IsColimitPresentation` for `𝒢` over its own system of
restrictions: the sheaf at the level `i` of that system *is* `uᵢ^{op} ⋙ 𝒢`, so the leg at `i` is
the identity, and compatibility says that the transition of the system is the canonical transport
— which is `RestrictionSystem.restrictComp_inv_hom_eq_eqToHom`.

The second clause, that every compatible family factors uniquely through these legs, is not
proved here. -/
theorem isCompatible_restrictionSystem (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w}
    [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (K : Precoverage C) [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
    (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t})) :
    IsCompatible.{v, u, w, t} D uC hu (restrictionSystem.{v, u, w, t} D uC hu K 𝒢) 𝒢.obj
      (fun _ => 𝟙 _) := by
  intro j k a
  rw [transition_restrictionSystem, RestrictionSystem.restrictComp_inv_hom_eq_eqToHom]
  exact (RestrictionSystem.eqToHom_symm_comp_whiskerLeft_id_comp_eqToHom _ _ _).symm

/-- The compatibility of a family out of the canonical restriction system, read in the
componentwise form that `ColimitPresheafDescent.General` asks for. -/
theorem hg_of_isCompatible (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w}
    [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (K : Precoverage C) [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
    (𝒢 H : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (gg : ∀ j, ((restrictionSystem.{v, u, w, t} D uC hu K 𝒢).obj j).obj ⟶ (uC j).op ⋙ H.obj)
    (hcomp : IsCompatible.{v, u, w, t} D uC hu
      (restrictionSystem.{v, u, w, t} D uC hu K 𝒢) H.obj gg)
    {i j : D.I} (a : j ⟶ i) (V : D.C i) :
    (gg i).app (op V) =
      𝒢.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V).symm)) ≫
        (gg j).app (op ((D.u a).obj V)) ≫
          H.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V))) := by
  have h := hcomp a
  rw [transition_restrictionSystem, RestrictionSystem.restrictComp_inv_hom_eq_eqToHom] at h
  refine Eq.trans (congrArg (fun α => α.app (op V)) h) ?_
  refine Eq.trans (RestrictionSystem.comp_app_of_eqToHom (D.u a).op
    (restrict_eq.{v, u, w, t} D uC hu a 𝒢.obj)
    (restrict_eq.{v, u, w, t} D uC hu a H.obj) (gg j) (op V)) ?_
  rw [eqToHom_map, eqToHom_map]
  rfl

open CategoryTheory.Sites.InverseSystem.Stacks.WeakSites.ColimitPresheafDescent in
/-- **A sheaf on the colimit site presents the colimit of its own system of restrictions.** This
is `IsColimitPresentation` for `𝒢` over `restrictionSystem`, with the identity legs — the second
conclusion of [Stacks, Tag 0EYN] in the form Stacks 09YP consumes it, and what the `hcolim`
hypothesis of Stacks 09YQ asks for.

The first clause is `isCompatible_restrictionSystem`. The second is the universal property, and it
is exactly the descent of `ColimitPresheafDescent.General` at the coefficient category
`Ab.{max u v w t}`: a compatible family out of the restrictions is a level-wise compatible family
of maps of presheaves on `C`, so it descends to a unique map `𝒢 ⟶ H` restricting to it. The two
inputs `hobj` and `hhom` — every object of the colimit site comes from a level, and every morphism
between images of objects of one level is, after a transition, the image of a morphism there — are
two of the five inputs of Stacks 09YP, so they are hypotheses here as they are there.

As in `restrictionSystem`, each `uC i` is assumed continuous for the topology of its level and
that of the colimit site; this is what makes the restrictions sheaves and does not follow from the
five inputs of Stacks 09YP. -/
theorem isColimitPresentation_restrictionSystem (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (K : Precoverage C) [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
    (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (uC i).obj Y = X)
    (hhom : ∀ (i : D.I) (X Y : D.C i) (f : (uC i).obj X ⟶ (uC i).obj Y),
      ∃ (j : D.I) (a : j ⟶ i) (φ : (D.u a).obj X ⟶ (D.u a).obj Y),
        (uC j).map φ = eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫
          eqToHom (Functor.congr_obj (hu a) Y).symm) :
    IsColimitPresentation.{v, u, w, t} D uC hu K
      (restrictionSystem.{v, u, w, t} D uC hu K 𝒢) 𝒢 (fun _ => 𝟙 _) := by
  refine ⟨isCompatible_restrictionSystem.{v, u, w, t} D uC hu K 𝒢, ?_⟩
  intro H gg hcomp
  have hg := @hg_of_isCompatible.{v, u, w, t} D _ _ uC hu K _ 𝒢 H gg hcomp
  refine ⟨ObjectProperty.homMk (General.natTrans D uC hu gg hg hobj hhom), ?_, ?_⟩
  · intro j
    refine Eq.trans (Category.id_comp _) (NatTrans.ext (funext fun U => ?_))
    obtain ⟨V⟩ := U
    exact General.natTrans_app_obj D uC hu gg hg hobj hhom j V
  · intro h' hh'
    refine Sheaf.hom_ext ?_
    refine General.eq_natTrans D uC hu gg hg hobj hhom h'.hom ?_
    intro i V
    have hi := hh' i
    simp only at hi
    exact (congrArg (fun α => α.app (op V)) hi).symm

end RestrictionSystem

end Stacks.WeakSites.ColimitSiteCohomology

end
