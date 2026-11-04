module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification inverts a map of presheaves of modules which is a quasi-isomorphism locally

A map of complexes of presheaves of modules whose value over each object of a covering sieve is
a quasi-isomorphism need not be a quasi-isomorphism: its homology presheaves are only *locally*
isomorphic. After sheafification it becomes one, and that is what this file proves.

The route is the one the homology of a sheaf complex is computed by in any case.
Sheafification of presheaves of modules is exact, so it carries the homology presheaves to the
homology sheaves; a map of presheaves of modules which is bijective over every object of a
covering sieve of every object is locally bijective, hence inverted by sheafification
(`CategoryTheory.GrothendieckTopology.W_of_isLocallyBijective`); and evaluation at an object is
exact, so the value of a homology presheaf over an object is the homology of the complex of
sections. Both uses of exactness are the same statement about a functor preserving homology, and
it is proved here once, as
`CategoryTheory.HomologicalComplex.quasiIsoAt_map_iff_isIso_map_homologyMap`.

## Main results

* `CategoryTheory.HomologicalComplex.quasiIsoAt_map_iff_isIso_map_homologyMap`: for a functor
  preserving homology, the image of a map of complexes is a quasi-isomorphism in a degree
  exactly when the image of the map of homology objects in that degree is invertible.
* `CategoryTheory.HomologicalComplex.isIso_map_homologyMap_extendMap_iff` and
  `CategoryTheory.HomologicalComplex.isIso_map_homologyMap_extendMap`: the maps of homology
  objects of the extension by zero of a complex along an embedding of complex shapes, in a degree
  in the image of the embedding and outside it.
* `CategoryTheory.Presheaf.isLocallyInjective_of_exists_mem_sieve` and
  `CategoryTheory.Presheaf.isLocallySurjective_of_exists_mem_sieve`: a map of presheaves which
  is injective (resp. surjective) over every object of a covering sieve of every object is
  locally injective (resp. locally surjective).
* `PresheafOfModules.isIso_sheafification_map_of_exists_mem_sieve`: **sheafification inverts a
  map of presheaves of modules which is invertible over every object of a covering sieve of
  every object.**
* `PresheafOfModules.quasiIso_sheafification_map_of_exists_mem_sieve`: **sheafification carries
  a map of complexes of presheaves of modules whose homology presheaves are locally isomorphic
  to a quasi-isomorphism.**

## Implementation notes

The local hypotheses are stated as *one covering sieve per object* rather than as a family
covering the final object, which is the form
`AlgebraicGeometry.RingedSite.exists_mem_sieve_span_eq` produces them in. The two are
interchangeable — `CategoryTheory.Presheaf.isLocallyInjective_of_coversTop` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalDual.lean` is the other form — but
with a sieve for each object no transitivity of the topology is needed: the sieve produced at an
object is already contained in the equalizer or image sieve the local condition asks about, so
`CategoryTheory.GrothendieckTopology.superset_covering` finishes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' u' v u

namespace HomologicalComplex

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  {B : Type u'} [Category.{v'} B] [Preadditive B] [CategoryWithHomology B]
  {ι : Type*} {cs : ComplexShape ι} {K L : HomologicalComplex A cs} (φ : K ⟶ L)
  (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- **A functor preserving homology carries a map of complexes to a quasi-isomorphism in a
degree exactly when it carries the map of homology objects in that degree to an isomorphism.**

This is the naturality of `CategoryTheory.ShortComplex.mapHomologyIso`, the comparison of the
homology of the image of a short complex with the image of its homology, at the short complex
cut out of the two complexes in that degree. -/
theorem quasiIsoAt_map_iff_isIso_map_homologyMap (i : ι) :
    QuasiIsoAt ((F.mapHomologicalComplex cs).map φ) i ↔ IsIso (F.map (homologyMap φ i)) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (MorphismProperty.isomorphisms B).arrow_mk_iso_iff
    (Arrow.isoMk (ShortComplex.mapHomologyIso ((shortComplexFunctor A cs i).obj K) F)
      (ShortComplex.mapHomologyIso ((shortComplexFunctor A cs i).obj L) F)
      (ShortComplex.mapHomologyIso_hom_naturality ((shortComplexFunctor A cs i).map φ) F).symm)

section Extend

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A] [HasZeroObject A]
  {B : Type u'} [Category.{v'} B]
  {ι ι' : Type*} {cs : ComplexShape ι} {cs' : ComplexShape ι'}
  {K L : HomologicalComplex A cs} (ψ : K ⟶ L) (emb : cs.Embedding cs') (G : A ⥤ B)

/-- **In a degree in the image of the embedding, the map of homology objects of the extension by
zero is the map of homology objects of the original complex**, read through
`HomologicalComplex.extendHomologyIso`; so a functor inverts one exactly when it inverts the
other. -/
theorem isIso_map_homologyMap_extendMap_iff {n : ι} {n' : ι'} (hn : emb.f n = n') :
    IsIso (G.map (homologyMap (extendMap ψ emb) n')) ↔ IsIso (G.map (homologyMap ψ n)) :=
  (MorphismProperty.isomorphisms B).arrow_mk_iso_iff
    (Arrow.isoMk (G.mapIso (K.extendHomologyIso emb hn))
      (G.mapIso (L.extendHomologyIso emb hn))
      (by
        have h := extendHomologyIso_hom_naturality ψ emb hn
        dsimp
        rw [← G.map_comp, ← G.map_comp, h]))

/-- **Outside the image of the embedding the extension by zero is exact**, so a functor inverts
the map of homology objects there for any reason at all. -/
theorem isIso_map_homologyMap_extendMap (n' : ι') (hn' : ∀ n, emb.f n ≠ n') :
    IsIso (G.map (homologyMap (extendMap ψ emb) n')) := by
  have : QuasiIsoAt (extendMap ψ emb) n' :=
    (quasiIsoAt_iff_exactAt _ _ (extend_exactAt _ _ _ hn')).2 (extend_exactAt _ _ _ hn')
  have : IsIso (homologyMap (extendMap ψ emb) n') := by
    rwa [← quasiIsoAt_iff_isIso_homologyMap]
  infer_instance

end Extend

end HomologicalComplex

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
  {F₁ F₂ : Cᵒᵖ ⥤ D} (φ : F₁ ⟶ F₂)

/-- **A map of presheaves which is injective over every object of a covering sieve of every
object is locally injective.** -/
theorem isLocallyInjective_of_exists_mem_sieve
    (h : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃Y : C⦄ (a : Y ⟶ V), S a →
      Function.Injective (φ.app (op Y))) :
    IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y hxy := by
    obtain ⟨S, hS, hinj⟩ := h X.unop
    refine J.superset_covering (fun Y a ha => ?_) hS
    show F₁.map a.op x = F₁.map a.op y
    refine hinj a ha ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]

/-- **A map of presheaves which is surjective over every object of a covering sieve of every
object is locally surjective.** -/
theorem isLocallySurjective_of_exists_mem_sieve
    (h : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃Y : C⦄ (a : Y ⟶ V), S a →
      Function.Surjective (φ.app (op Y))) :
    IsLocallySurjective J φ where
  imageSieve_mem {X} s := by
    obtain ⟨S, hS, hsurj⟩ := h X
    exact J.superset_covering (fun Y a ha => hsurj a ha (F₂.map a.op s)) hS

end CategoryTheory.Presheaf

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- **Sheafification inverts a map of presheaves of modules which is invertible over every
object of a covering sieve of every object.**

The underlying map of presheaves of abelian groups is locally bijective, hence belongs to the
class of maps sheafification inverts; and a map of sheaves of modules is invertible as soon as
its underlying map of sheaves of abelian groups is. -/
theorem isIso_sheafification_map_of_exists_mem_sieve {M N : PresheafOfModules.{v} R₀} (u : M ⟶ N)
    (h : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃Y : C⦄ (a : Y ⟶ V), S a → IsIso (u.app (op Y))) :
    IsIso ((sheafification.{v} α).map u) := by
  have hinj : Presheaf.IsLocallyInjective J ((toPresheaf.{v} R₀).map u) :=
    Presheaf.isLocallyInjective_of_exists_mem_sieve J _ fun V => (h V).imp fun _ ⟨hS, hiso⟩ =>
      ⟨hS, fun _ a ha => ((ConcreteCategory.isIso_iff_bijective _).1 (hiso a ha)).1⟩
  have hsurj : Presheaf.IsLocallySurjective J ((toPresheaf.{v} R₀).map u) :=
    Presheaf.isLocallySurjective_of_exists_mem_sieve J _ fun V => (h V).imp fun _ ⟨hS, hiso⟩ =>
      ⟨hS, fun _ a ha => ((ConcreteCategory.isIso_iff_bijective _).1 (hiso a ha)).2⟩
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{v} R)]
  exact (J.W_iff _).mp (J.W_of_isLocallyBijective ((toPresheaf.{v} R₀).map u))

variable [HasSheafify J AddCommGrpCat.{v}]

/-- Sheafification of presheaves of modules is additive, being a left adjoint. -/
instance additive_sheafification : (sheafification.{v} α).Additive :=
  (sheafificationAdjunction.{v} α).left_adjoint_additive

/-- Sheafification of presheaves of modules preserves finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_sheafification :
    PreservesFiniteColimits (sheafification.{v} α) :=
  have : PreservesColimitsOfSize.{0, 0} (sheafification.{v} α) :=
    (sheafificationAdjunction.{v} α).leftAdjoint_preservesColimits
  inferInstance

/-- **Sheafification of presheaves of modules preserves homology**, being exact: it preserves
finite limits because sheafification is left exact, and finite colimits because it is a left
adjoint. -/
instance preservesHomology_sheafification : (sheafification.{v} α).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- **Sheafification carries a map of complexes of presheaves of modules whose homology
presheaves are locally isomorphic to a quasi-isomorphism.**

Sheafification preserves homology, so by
`CategoryTheory.HomologicalComplex.quasiIsoAt_map_iff_isIso_map_homologyMap` the conclusion is
that it inverts each map of homology presheaves, which is
`PresheafOfModules.isIso_sheafification_map_of_exists_mem_sieve`. -/
theorem quasiIso_sheafification_map_of_exists_mem_sieve {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex (PresheafOfModules.{v} R₀) cs} (φ : K ⟶ L)
    (h : ∀ (n : ι) (V : C), ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃Y : C⦄ (a : Y ⟶ V), S a →
      IsIso ((HomologicalComplex.homologyMap φ n).app (op Y))) :
    QuasiIso (((sheafification.{v} α).mapHomologicalComplex cs).map φ) := by
  rw [quasiIso_iff]
  intro n
  rw [HomologicalComplex.quasiIsoAt_map_iff_isIso_map_homologyMap]
  exact isIso_sheafification_map_of_exists_mem_sieve α _ (h n)

/-- The value of a map of homology presheaves over an object is invertible exactly when the
complex of sections over that object is carried to a quasi-isomorphism: evaluation at an object
is exact. -/
theorem isIso_homologyMap_app_iff {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex (PresheafOfModules.{v} R₀) cs} (φ : K ⟶ L) (n : ι) (V : Cᵒᵖ) :
    IsIso ((HomologicalComplex.homologyMap φ n).app V) ↔
      QuasiIsoAt (((evaluation.{v} R₀ V).mapHomologicalComplex cs).map φ) n :=
  (HomologicalComplex.quasiIsoAt_map_iff_isIso_map_homologyMap φ (evaluation.{v} R₀ V) n).symm

end PresheafOfModules

end
