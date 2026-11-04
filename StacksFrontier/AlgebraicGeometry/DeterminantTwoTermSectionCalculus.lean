module

public import StacksFrontier.AlgebraicGeometry.RestrictPushforwardCoherence

/-!
# Section calculus for the determinant on the affine opens of a scheme

The construction of the determinant of Stacks 0FJX on an arbitrary scheme is assembled from the
affine opens of `X`, and every stage of that assembly -- the chart comparisons, the glueing datum,
the canonical global section and its compatibility with isomorphisms -- is checked by evaluating
sheaves of modules on an open and chasing *sections*. This module is the one home for the
section-level calculus those stages share: restriction of a section along an inclusion of opens,
the restriction of a global section, how a morphism of sheaves of modules commutes with both, and
how the sections map of a composite, an inverse, a two-fold composite and the image of an
isomorphism under a restriction functor are read off.

Nothing here mentions a determinant, an affine open or a derived category: every declaration is
stated for an arbitrary scheme `Y`, arbitrary `Y.Modules` and arbitrary opens, so that an instance
of it needs no reduction at the point of use. That is deliberate. The calculus was previously
written twice, once by the module that reads the canonical element on a chart and once by the
module that reads the canonical global section, and the two copies were identical; collecting it
here is what keeps a third copy from being written.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.resSec`: the restriction of a section of a sheaf of
  modules along an inclusion of opens.
* `AlgebraicGeometry.DeterminantTwoTerm.globalRes`: the restriction of a global section to an
  open.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.resSec_resSec` and
  `AlgebraicGeometry.DeterminantTwoTerm.resSec_globalRes`: restrictions compose.
* `AlgebraicGeometry.DeterminantTwoTerm.resSec_eq`: every restriction map of a sheaf of modules
  between two opens is the canonical one, the homs of a poset being unique.
* `AlgebraicGeometry.DeterminantTwoTerm.app_resSec` and
  `AlgebraicGeometry.DeterminantTwoTerm.app_globalRes`: a morphism of sheaves of modules commutes
  with restriction of a section and of a global section.
* `AlgebraicGeometry.DeterminantTwoTerm.restrict_resSec` and
  `AlgebraicGeometry.DeterminantTwoTerm.pushforward_resSec`: a restriction map of a restriction
  along an open immersion, and of a pushforward, is a restriction map of the module itself.
* `AlgebraicGeometry.DeterminantTwoTerm.comp_app_apply`,
  `AlgebraicGeometry.DeterminantTwoTerm.twoIsoHom_app`,
  `AlgebraicGeometry.DeterminantTwoTerm.inv_app_apply_eq` and
  `AlgebraicGeometry.DeterminantTwoTerm.symm_hom_app_apply_eq`: the sections map of a composite,
  of a two-fold composite of isomorphisms, and of an inverse.
* `AlgebraicGeometry.DeterminantTwoTerm.app_square` and
  `AlgebraicGeometry.DeterminantTwoTerm.app_mapIso_naturality`: a commuting square of morphisms
  of sheaves of modules, and the naturality of a natural isomorphism of functors between
  categories of sheaves of modules, read on a section.
* `AlgebraicGeometry.DeterminantTwoTerm.restrictFunctor_mapIso_apply`: the component of the image
  of an isomorphism under a restriction functor is the component of that isomorphism at the image
  open.

## References

* [Stacks Project, Lemma 36.10.11 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

/-- The restriction of a section along an inclusion of opens. -/
def resSec {Y : Scheme.{u}} (M : Y.Modules) {P Q : Y.Opens} (hPQ : P ≤ Q)
    (s : ToType (M.val.obj (op Q))) : ToType (M.val.obj (op P)) :=
  M.val.map (homOfLE hPQ).op s

/-- The restriction of a global section to an open. -/
def globalRes {Y : Scheme.{u}} (M : Y.Modules) (P : Y.Opens)
    (s : ToType (M.val.obj (op (⊤ : Y.Opens)))) : ToType (M.val.obj (op P)) :=
  M.val.map (homOfLE le_top).op s

/-- Two restrictions compose to one. -/
theorem resSec_resSec {Y : Scheme.{u}} (M : Y.Modules) {P Q R : Y.Opens} (h₁ : Q ≤ R)
    (h₂ : P ≤ Q) (h₃ : P ≤ R) (s : ToType (M.val.obj (op R))) :
    resSec M h₂ (resSec M h₁ s) = resSec M h₃ s := by
  rw [resSec, resSec, resSec, Subsingleton.elim (homOfLE h₃).op
    ((homOfLE h₁).op ≫ (homOfLE h₂).op), M.val.map_comp]
  rfl

/-- Restricting a restricted global section again gives a restricted global section. -/
theorem resSec_globalRes {Y : Scheme.{u}} (M : Y.Modules) {P Q : Y.Opens} (hQP : Q ≤ P)
    (s : ToType (M.val.obj (op (⊤ : Y.Opens)))) :
    resSec M hQP (globalRes M P s) = globalRes M Q s :=
  resSec_resSec M le_top hQP le_top s

/-- Any restriction map of a module between two opens is the canonical one, the homs of a poset
being unique. -/
theorem resSec_eq {Y : Scheme.{u}} (M : Y.Modules) {P Q : (Y.Opens)ᵒᵖ} (a : P ⟶ Q)
    (hPQ : Q.unop ≤ P.unop) (s : ToType (M.val.obj P)) :
    M.val.map a s = resSec M hPQ s := by
  rw [resSec, Subsingleton.elim a (homOfLE hPQ).op]

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
theorem app_resSec {Y : Scheme.{u}} {A B : Y.Modules} (φ : A ⟶ B) {P Q : Y.Opens}
    (hPQ : P ≤ Q) (s : ToType (A.val.obj (op Q))) :
    Scheme.Modules.Hom.app φ P (resSec A hPQ s) =
      resSec B hPQ (Scheme.Modules.Hom.app φ Q s) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hPQ).op) s

/-- A morphism of sheaves of modules commutes with restriction of a global section. -/
theorem app_globalRes {Y : Scheme.{u}} {A B : Y.Modules} (φ : A ⟶ B) (P : Y.Opens)
    (s : ToType (A.val.obj (op (⊤ : Y.Opens)))) :
    Scheme.Modules.Hom.app φ P (globalRes A P s) =
      globalRes B P (Scheme.Modules.Hom.app φ ⊤ s) :=
  app_resSec φ le_top s

/-- A restriction map of a restriction along an open immersion is a restriction map of the
module, between the image opens. -/
theorem restrict_resSec {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    (M : Z.Modules) {P Q : Y.Opens} (hPQ : P ≤ Q) (hI : f ''ᵁ P ≤ f ''ᵁ Q)
    (s : ToType (M.val.obj (op (f ''ᵁ Q)))) :
    resSec (Scheme.Modules.restrict M f) hPQ s = resSec M hI s :=
  resSec_eq M (f.opensFunctor.map (homOfLE hPQ)).op hI s

/-- A restriction map of a pushforward is a restriction map of the module, between the preimage
opens. -/
theorem pushforward_resSec {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Y.Modules)
    {P Q : Z.Opens} (hPQ : P ≤ Q) (hI : f ⁻¹ᵁ P ≤ f ⁻¹ᵁ Q)
    (s : ToType (M.val.obj (op (f ⁻¹ᵁ Q)))) :
    resSec ((Scheme.Modules.pushforward f).obj M) hPQ s = resSec M hI s :=
  resSec_eq M ((TopologicalSpace.Opens.map f.base).map (homOfLE hPQ)).op hI s

/-- The sections map of a composite is the composite of the sections maps. -/
theorem comp_app_apply {Y : Scheme.{u}} {A B C : Y.Modules} (φ : A ⟶ B) (ψ : B ⟶ C)
    (U : Y.Opens) (s : ToType (A.val.obj (op U))) :
    Scheme.Modules.Hom.app (φ ≫ ψ) U s =
      Scheme.Modules.Hom.app ψ U (Scheme.Modules.Hom.app φ U s) := rfl

/-- The sections map of a two-fold composite of isomorphisms. Isolated on variables. -/
theorem twoIsoHom_app {Y : Scheme.{u}} {A B C : Y.Modules} (i : A ≅ B) (j : B ≅ C)
    (U : Y.Opens) (s : ToType (A.val.obj (op U))) :
    Scheme.Modules.Hom.app (i ≪≫ j).hom U s =
      Scheme.Modules.Hom.app j.hom U (Scheme.Modules.Hom.app i.hom U s) := rfl

/-- The sections map of the inverse of an isomorphism, read off the sections map of the
isomorphism. -/
theorem inv_app_apply_eq {Y : Scheme.{u}} {A B : Y.Modules} (φ : A ≅ B) (P : Y.Opens)
    (x : ToType (A.val.obj (op P))) (y : ToType (B.val.obj (op P)))
    (hxy : Scheme.Modules.Hom.app φ.hom P x = y) :
    Scheme.Modules.Hom.app φ.inv P y = x := by
  subst hxy
  refine ConcreteCategory.congr_hom (?_ :
    Scheme.Modules.Hom.app φ.hom P ≫ Scheme.Modules.Hom.app φ.inv P = 𝟙 _) x
  rw [← Scheme.Modules.Hom.comp_app, φ.hom_inv_id, Scheme.Modules.Hom.id_app]

/-- `AlgebraicGeometry.DeterminantTwoTerm.inv_app_apply_eq`, with the backward map written as the
forward map of the symmetric isomorphism. Isolated on variables so that the two spellings are
never reconciled at a concrete isomorphism. -/
theorem symm_hom_app_apply_eq {Y : Scheme.{u}} {A B : Y.Modules} (φ : A ≅ B)
    (P : Y.Opens) (x : ToType (A.val.obj (op P))) (y : ToType (B.val.obj (op P)))
    (hxy : Scheme.Modules.Hom.app φ.hom P x = y) :
    Scheme.Modules.Hom.app φ.symm.hom P y = x :=
  inv_app_apply_eq φ P x y hxy

/-- **A commuting square of morphisms of sheaves of modules, read on a section.** Stated on
variables, so that an instance of it needs no reduction. -/
theorem app_square {Y : Scheme.{u}} {A B B' C : Y.Modules} (u : A ⟶ B) (v : B ⟶ B')
    (w : A ⟶ C) (t : C ⟶ B') (sq : u ≫ v = w ≫ t) (U : Y.Opens)
    (s : ToType (A.val.obj (op U))) :
    Scheme.Modules.Hom.app v U (Scheme.Modules.Hom.app u U s) =
      Scheme.Modules.Hom.app t U (Scheme.Modules.Hom.app w U s) :=
  (comp_app_apply u v U s).symm.trans
    ((ConcreteCategory.congr_hom (congrArg (fun ψ => Scheme.Modules.Hom.app ψ U) sq) s).trans
      (comp_app_apply w t U s))

/-- **The naturality of a natural isomorphism of functors between categories of sheaves of
modules, read on a section.** Every datum is a variable, so an instance of this lemma needs no
reduction; it is instantiated at
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
theorem app_mapIso_naturality {Y Z : Scheme.{u}} {F G : Z.Modules ⥤ Y.Modules}
    (ν : F ≅ G) {M N : Z.Modules} (χ : M ≅ N) (U : Y.Opens)
    (s : ToType ((F.obj M).val.obj (op U))) :
    Scheme.Modules.Hom.app (G.mapIso χ).hom U (Scheme.Modules.Hom.app (ν.app M).hom U s) =
      Scheme.Modules.Hom.app (ν.app N).hom U
        (Scheme.Modules.Hom.app (F.mapIso χ).hom U s) :=
  (app_square (F.mapIso χ).hom (ν.app N).hom (ν.app M).hom (G.mapIso χ).hom
    (ν.hom.naturality χ.hom) U s).symm

/-- The component of the image of an isomorphism under a restriction functor. -/
theorem restrictFunctor_mapIso_apply {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    {M N : Z.Modules} (i : M ≅ N) (U : Y.Opens) (s : ToType (M.val.obj (op (f ''ᵁ U)))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor f).mapIso i).hom U s =
      Scheme.Modules.Hom.app i.hom (f ''ᵁ U) s := rfl

end AlgebraicGeometry.DeterminantTwoTerm
