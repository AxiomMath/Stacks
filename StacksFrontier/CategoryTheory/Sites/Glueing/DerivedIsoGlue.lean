module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.Algebra.Homology.DerivedCategory.QuasiIsoFromDerivedIso
public import StacksFrontier.CategoryTheory.Sites.Glueing.MapsOfSheavesGlue

/-!
# Gluing isomorphisms of the derived category along a jointly full family of exact functors

Let `𝒜` be an abelian category and `E i : 𝒜 ⥤ ℬ i` a family of exact functors to abelian
categories which jointly reflect isomorphisms. Then they jointly reflect quasi-isomorphisms of
complexes. If moreover the family is jointly faithful and *jointly full* on the terms of two
complexes `P` and `B` — every family of morphisms `E i (P^k) ⟶ E i (B^k)` comes from one morphism
`P^k ⟶ B^k` — and each `E i P` is a bounded above complex of projectives, then isomorphisms
`Q(E i P) ≅ Q(E i B)` in the derived categories of the `ℬ i`, with no compatibility between them,
give an isomorphism `Q(P) ≅ Q(B)`: each of them comes from a quasi-isomorphism of complexes, these
glue degreewise to a morphism `P ⟶ B`, and that morphism is a quasi-isomorphism because its images
are.

The example to keep in mind is the restriction of sheaves on the slice site `C/U` to the slices
`C/U i` of the members of a covering `{U i ⟶ U}`: these restrictions jointly reflect
isomorphisms (`CategoryTheory.Sheaf.isIso_of_isIso_overMapPullback_map`), and when the covering is
a decomposition into disjoint pieces, maps of sheaves glue with no compatibility condition.

## Main results

* `HomologicalComplex.isIso_map_homologyMap_of_quasiIsoAt_map`: for a functor preserving
  homology, the image of a homology map of `φ` is invertible when the image of `φ` is a
  quasi-isomorphism in that degree.
* `HomologicalComplex.quasiIso_of_forall_quasiIso_map`: a family of homology-preserving functors
  jointly reflecting isomorphisms jointly reflects quasi-isomorphisms.
* `DerivedCategory.nonempty_Q_obj_iso_of_forall_iso_map`: the gluing statement above.
* `CategoryTheory.Sheaf.isIso_of_isIso_overMapPullback_map`: a morphism of sheaves on `C/U`
  whose restriction to every member of a covering of `U` is invertible is invertible.
* `Stacks.SheafMapGluing.overMapPullbackComplexIso`: restricting a complex of sheaves to `C/U` and
  then along `U' ⟶ U` is restricting it to `C/U'`.
* `Stacks.SheafMapGluing.nonempty_Q_obj_overPullback_iso_of_hom`: an isomorphism of the derived
  category between the restrictions of two complexes to `C/U` restricts to `C/U'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w

namespace HomologicalComplex

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Abelian C₁] [Abelian C₂]
  {ι : Type*} {c : ComplexShape ι}

/-- **The image of a homology map under a homology-preserving functor.** If `F` preserves
homology and `F(φ)` is a quasi-isomorphism in degree `n`, then `F` carries the degree-`n`
homology map of `φ` to an isomorphism: the comparison `CategoryTheory.ShortComplex.mapHomologyIso`
identifies the two. -/
theorem isIso_map_homologyMap_of_quasiIsoAt_map (F : C₁ ⥤ C₂) [F.Additive]
    [F.PreservesHomology] {K L : HomologicalComplex C₁ c} (φ : K ⟶ L) (n : ι)
    (hφ : QuasiIsoAt ((F.mapHomologicalComplex c).map φ) n) :
    IsIso (F.map (homologyMap φ n)) := by
  have hmid : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map
      ((shortComplexFunctor C₁ c n).map φ))) := by
    rw [← ShortComplex.quasiIso_iff]
    exact (quasiIsoAt_iff ((F.mapHomologicalComplex c).map φ) n).1 hφ
  have h2 : IsIso ((((shortComplexFunctor C₁ c n).obj K).mapHomologyIso F).hom ≫
      F.map (ShortComplex.homologyMap ((shortComplexFunctor C₁ c n).map φ))) := by
    rw [← ShortComplex.mapHomologyIso_hom_naturality (F := F)
      (φ := (shortComplexFunctor C₁ c n).map φ)]
    infer_instance
  have hK := (((shortComplexFunctor C₁ c n).obj K).mapHomologyIso F).isIso_hom
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hK h2

/-- **Quasi-isomorphisms are detected by a family of exact functors jointly reflecting
isomorphisms.** Let `E i : C₁ ⥤ C₂ i` be additive functors preserving homology such that a
morphism `ψ` of `C₁` is invertible as soon as every `E i ψ` is. A morphism of complexes whose
images under all the `E i` are quasi-isomorphisms is a quasi-isomorphism. -/
theorem quasiIso_of_forall_quasiIso_map {κ : Type*} {D : κ → Type*} [∀ i, Category (D i)]
    [∀ i, Abelian (D i)] (E : ∀ i, C₁ ⥤ D i) [∀ i, (E i).Additive] [∀ i, (E i).PreservesHomology]
    (hE : ∀ {X Y : C₁} (ψ : X ⟶ Y), (∀ i, IsIso ((E i).map ψ)) → IsIso ψ)
    {K L : HomologicalComplex C₁ c} (φ : K ⟶ L)
    (hφ : ∀ i, QuasiIso (((E i).mapHomologicalComplex c).map φ)) : QuasiIso φ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact hE _ fun i => isIso_map_homologyMap_of_quasiIsoAt_map (E i) φ n ((hφ i).quasiIsoAt n)

end HomologicalComplex

namespace DerivedCategory

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
  {κ : Type*} {ℬ : κ → Type*} [∀ i, Category (ℬ i)] [∀ i, Abelian (ℬ i)]
  [∀ i, HasDerivedCategory (ℬ i)]

/-- **Gluing isomorphisms of derived categories along a jointly full family of exact functors.**
Let `E i : 𝒜 ⥤ ℬ i` be additive functors between abelian categories which preserve homology and
jointly reflect isomorphisms, and let `P`, `B` be complexes of `𝒜` such that

* the `E i` are jointly faithful on morphisms `P^k ⟶ B^l`,
* every family of morphisms `E i (P^k) ⟶ E i (B^k)` is the image of one morphism `P^k ⟶ B^k`,
* each `E i P` is bounded above with projective terms.

Then isomorphisms `Q(E i P) ≅ Q(E i B)`, one for each `i` and with no compatibility between
them, give an isomorphism `Q(P) ≅ Q(B)`.

Each given isomorphism is induced by a quasi-isomorphism `g i : E i P ⟶ E i B`
(`CochainComplex.exists_quasiIso_of_derived_iso`); the degreewise components of the `g i` glue to
morphisms `P^k ⟶ B^k`, which commute with the differentials by joint faithfulness; and the
resulting morphism of complexes is a quasi-isomorphism since its images `g i` are
(`HomologicalComplex.quasiIso_of_forall_quasiIso_map`). -/
theorem nonempty_Q_obj_iso_of_forall_iso_map (E : ∀ i, 𝒜 ⥤ ℬ i) [∀ i, (E i).Additive]
    [∀ i, (E i).PreservesHomology]
    (hE : ∀ {X Y : 𝒜} (ψ : X ⟶ Y), (∀ i, IsIso ((E i).map ψ)) → IsIso ψ)
    (P B : CochainComplex 𝒜 ℤ)
    (hfaith : ∀ (k l : ℤ) (φ ψ : P.X k ⟶ B.X l), (∀ i, (E i).map φ = (E i).map ψ) → φ = ψ)
    (hglue : ∀ (k : ℤ) (φ : ∀ i, (E i).obj (P.X k) ⟶ (E i).obj (B.X k)),
      ∃ ψ : P.X k ⟶ B.X k, ∀ i, (E i).map ψ = φ i)
    (d : κ → ℤ)
    [∀ i, CochainComplex.IsStrictlyLE
      (((E i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) (d i)]
    [∀ i n, Projective ((((E i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n)]
    (e : ∀ i, Q.obj (((E i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      Q.obj (((E i).mapHomologicalComplex (ComplexShape.up ℤ)).obj B)) :
    Nonempty (Q.obj P ≅ Q.obj B) := by
  choose g hg using fun i => CochainComplex.exists_quasiIso_of_derived_iso _ _ (d i) (e i)
  choose ψ hψ using fun k => hglue k fun i => (g i).f k
  let Ψ : P ⟶ B :=
    { f := ψ
      comm' := fun k l _ => hfaith k l _ _ fun i => by
        simp only [Functor.map_comp, hψ]
        exact (g i).comm k l }
  have hΨ (i : κ) : ((E i).mapHomologicalComplex (ComplexShape.up ℤ)).map Ψ = g i := by
    ext k
    exact hψ k i
  have : QuasiIso Ψ :=
    HomologicalComplex.quasiIso_of_forall_quasiIso_map E hE Ψ fun i => by
      rw [hΨ i]
      exact hg i
  exact ⟨asIso (Q.map Ψ)⟩

end DerivedCategory

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] (J : GrothendieckTopology C) {A : Type*} [Category A]

/-- **Invertibility of a morphism of sheaves on a slice site is local along a covering.** Let
`{f i : V i ⟶ U}` generate a covering sieve of `U`. A morphism of sheaves on the slice site `C/U`
whose restriction to the slice site `C/V i` along each `f i` is invertible is invertible.

The objects `f i` of `C/U` cover its final object, so by
`CategoryTheory.Sheaf.isIso_of_coversTop` it suffices that the restrictions to the iterated slices
`(C/U)/f i` are invertible; their components are components of the given morphism at objects of
`C/U` mapping to `f i`, each isomorphic to the image of an object of `C/V i`. -/
theorem isIso_of_isIso_overMapPullback_map {U : C} {ι : Type*} {V : ι → C} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U) {F G : Sheaf (J.over U) A} (φ : F ⟶ G)
    (h : ∀ i, IsIso ((J.overMapPullback A (f i)).map φ)) : IsIso φ := by
  refine Sheaf.isIso_of_coversTop (X := fun i => Over.mk (f i)) (fun Y => ?_) fun i => ?_
  · rw [GrothendieckTopology.mem_over_iff]
    refine J.superset_covering (fun Z g hg => ?_) (J.pullback_stable Y.hom hf)
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    rw [Sieve.overEquiv_iff]
    exact ⟨i, ⟨Over.homMk a ha.symm⟩⟩
  · rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro Z
    have hZ := h i
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app] at hZ
    have e : Z.unop.left ≅ (Over.map (f i)).obj (Over.mk Z.unop.hom.left) :=
      Over.isoMk (Iso.refl _) (by simpa using Over.w Z.unop.hom)
    exact (NatTrans.isIso_app_iff_of_iso φ.hom e.op).1 (hZ (op (Over.mk Z.unop.hom.left)))

end CategoryTheory.Sheaf

namespace Stacks.SheafMapGluing

variable {C : Type*} [Category C] (J : GrothendieckTopology C)

section Complexes

variable {A : Type*} [Category A] [Preadditive A]

/-- Restricting a complex of sheaves to the slice site `C/U` and then along `a : U' ⟶ U` is
restricting it to `C/U'`: the degreewise components of
`Stacks.SheafMapGluing.overPullbackOverMapPullbackIso`. -/
noncomputable def overMapPullbackComplexIso {U U' : C} (a : U' ⟶ U)
    (K : CochainComplex (Sheaf J A) ℤ) :
    ((J.overMapPullback A a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((J.overPullback A U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((J.overPullback A U').mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k => (overPullbackOverMapPullbackIso J a (A := A)).app (K.X k))
    (fun _ _ _ => ((overPullbackOverMapPullbackIso J a (A := A)).hom.naturality _).symm)

end Complexes

section Derived

variable {Λ : Type*} [Ring Λ]

/-- **Restricting an isomorphism of the derived category to a smaller slice.** Let `a : U' ⟶ U`
be a morphism of the site such that restriction of sheaves of modules along it is exact. An
isomorphism `Q(P|_U) ≅ Q(B|_U)` in the derived category of sheaves of modules on `C/U` between
the restrictions of two complexes of sheaves on `C` gives an isomorphism `Q(P|_{U'}) ≅ Q(B|_{U'})`
on `C/U'`: apply the derived functor of the restriction along `a`, and use that restricting to
`C/U` and then along `a` is restricting to `C/U'`. -/
theorem nonempty_Q_obj_overPullback_iso_of_hom {U U' : C} (a : U' ⟶ U)
    [HasSheafify (J.over U) (ModuleCat.{w} Λ)]
    [HasSheafify (J.over U') (ModuleCat.{w} Λ)]
    [HasDerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ))]
    [HasDerivedCategory (Sheaf (J.over U') (ModuleCat.{w} Λ))]
    [PreservesFiniteLimits (J.overMapPullback (ModuleCat.{w} Λ) a)]
    [PreservesFiniteColimits (J.overMapPullback (ModuleCat.{w} Λ) a)]
    (P B : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (e : DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{w} Λ) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{w} Λ) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj B)) :
    Nonempty (DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{w} Λ) U').mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{w} Λ) U').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj B)) :=
  let Φ := J.overMapPullback (ModuleCat.{w} Λ) a
  ⟨DerivedCategory.Q.mapIso (overMapPullbackComplexIso J a P).symm ≪≫
    (Φ.mapDerivedCategoryFactors.app _).symm ≪≫ Φ.mapDerivedCategory.mapIso e ≪≫
      Φ.mapDerivedCategoryFactors.app _ ≪≫
        DerivedCategory.Q.mapIso (overMapPullbackComplexIso J a B)⟩

end Derived

end Stacks.SheafMapGluing
