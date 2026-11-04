module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp

/-!
# The two composition isomorphisms of the iterated derived stalk, against their comparisons

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and `x` a point of `X`.
`AlgebraicGeometry.derivedPullbackStalkIso_comp_of_kFlat` reduces the coherence of the derived
stalk formula of Stacks 0098 with the composition formula of Tag 0D5S to a single equation at a
K-flat complex.  That equation is a composite of eight morphisms, and two of the eight are
composition isomorphisms whose interaction with the surrounding comparisons nothing in the
development recorded:

* `AlgebraicGeometry.derivedStalkExtensionCompIso`, which merges the two derived
  extension-of-scalars functors along the germ maps of `g` at `f x` and of `f` at `x` into the one
  along the germ map of `f ≫ g`;
* `Stacks.ModuleSkyscraper.extendScalarsStalkComp`, the *underived* merge of the same two
  extensions of scalars, which is what `Stacks.ModuleSkyscraper.pullbackStalkIso_comp_app`
  produces.

This file records both interactions.  Each of the two isomorphisms is transported along the
equation `Stacks.ModuleSkyscraper.stalkMap_hom_comp` of ring homomorphisms, so each statement
carries an `eqToHom`; the two abstract lemmas below are what make those `eqToHom`s harmless, since
each is proved by substituting the equation away.

## Main definitions

There are no new definitions.

## Main results

* `StacksDraft.DerivedExtensionScalarsComp.leftAdjointCompIso_restrictScalarsComp'`: the
  composition isomorphism for extension of scalars produced by uniqueness of left adjoints from
  `ModuleCat.restrictScalarsComp'` is Mathlib's `ModuleCat.extendScalarsComp`, transported along
  the equation of ring homomorphisms.
* `Stacks.ModuleSkyscraper.extendScalarsStalkComp_eq` and
  `Stacks.ModuleSkyscraper.extendScalarsStalkComp_hom_app`: the same for the germ maps, which is
  the form Stacks 0098's composition compatibility is stated at.
* `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso_eqToIso_comp_comparison`:
  the characterizing equation of `derivedExtensionScalarsCompIso` survives the transport.
* `AlgebraicGeometry.derivedStalkExtensionCompIso_hom_app_comp_comparison`: **the merged
  extension-of-scalars tail.**  The two-step derived extension of scalars along the germ maps,
  read against the comparison of derived with degreewise extension of scalars along the germ map
  of `f ≫ g`, is the comparison for `g` at `f x`, then the comparison for `f` at `x`, then the
  degreewise merge.
* `Stacks.ModuleSkyscraper.modulesStalkFunctor_map_pullbackComp_hom_app` and
  `Stacks.ModuleSkyscraper.pullbackStalkIso_comp_inv_app`: **Stacks 0098's composition
  compatibility, read backwards.**  The stalk at `x` of the pullback-composition isomorphism,
  followed by the stalk formula for `f ≫ g` read backwards, is the two stalk formulas read
  backwards followed by the underived merge.

## Implementation notes

*Why the two abstract lemmas are stated for a free ring homomorphism and a free equation.*  Both
`Stacks.ModuleSkyscraper.extendScalarsStalkComp` and
`AlgebraicGeometry.derivedStalkExtensionCompIso` are built by transporting a composition
isomorphism along `Stacks.ModuleSkyscraper.stalkMap_hom_comp`, and the germ map of `f ≫ g` is not
a variable, so that equation cannot be substituted away in place.  Stated for a free `φ` with
`h : φ = b.comp a` it can: `subst h` turns every `eqToHom` into an identity, and what remains is
the untransported statement.  The two concrete corollaries then follow by `exact`, where the
conversion check runs at default transparency.

*Why the backwards form of Stacks 0098's composition compatibility is stated without an inverse
on the left.*  The natural statement composes the germ comparison with the inverse of the stalk
formula for `f ≫ g`, and `CategoryTheory.Iso.comp_inv_eq` does not rewrite it: the stalk of
`(f ≫ g)^*` is taken over `𝒪_{Z, (f ≫ g) x}` and the two-step one over `𝒪_{Z, g (f x)}`, and
`(f ≫ g) x` and `g (f x)` are definitionally but not *reducibly* equal, so the rewritten goal is
rejected as not type-correct.  `modulesStalkFunctor_map_pullbackComp_hom_app` states the form with
no inverse, where every rewrite acts on one spelling only; `pullbackStalkIso_comp_inv_app` moves
the isomorphism across it in term mode.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars

universe u

namespace StacksDraft.DerivedExtensionScalarsComp

attribute [local instance] HasDerivedCategory.standard

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- **The composition isomorphism for extension of scalars, transported along an equation of ring
homomorphisms.**  Let `a : R →+* S`, `b : S →+* T` and let `φ : R →+* T` be *equal* to `b ∘ a`
rather than that term.  The isomorphism `extendScalars a ⋙ extendScalars b ≅ extendScalars φ`
produced from `ModuleCat.restrictScalarsComp'` by uniqueness of left adjoints is Mathlib's
`ModuleCat.extendScalarsComp`, read backwards and transported along the equation.

Proved by substituting the equation, after which both sides are the mate of one and the same
isomorphism of restriction-of-scalars functors. -/
theorem leftAdjointCompIso_restrictScalarsComp'
    (a : R →+* S) (b : S →+* T) (φ : R →+* T) (h : φ = b.comp a) :
    Adjunction.leftAdjointCompIso (ModuleCat.extendRestrictScalarsAdj.{u, u, u} a)
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} b)
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ)
        (ModuleCat.restrictScalarsComp'.{u} a b φ h).symm =
      (ModuleCat.extendScalarsComp.{u} a b).symm ≪≫
        eqToIso (congrArg ModuleCat.extendScalars.{u} h.symm) := by
  subst h
  exact Iso.ext rfl

/-- **The characterizing equation of the composition isomorphism for *derived* extension of
scalars, transported along an equation of ring homomorphisms.**  This is
`derivedExtensionScalarsCompIso_hom_app_comp_comparison` with the target functor presented as
derived extension of scalars along a homomorphism `φ` merely *equal* to `b ∘ a`, which is how the
germ map of a composite presents itself.

Proved by substituting the equation, after which the two `eqToHom`s are identities. -/
theorem derivedExtensionScalarsCompIso_eqToIso_comp_comparison
    (a : R →+* S) (b : S →+* T) (φ : R →+* T) (h : φ = b.comp a)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtensionScalarsCompIso a b ≪≫
          eqToIso (congrArg
            (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor) h.symm)).hom.app
          (DerivedCategory.Q.obj C) ≫
        (totalDerivedExtensionScalars.{u, u, u} φ).comparison.app C =
      (totalDerivedExtensionScalars.{u, u, u} b).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} a).comparison.app C) ≫
        (totalDerivedExtensionScalars.{u, u, u} b).comparison.app
          (((ModuleCat.extendScalars a).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
        (extensionScalarsComplexCompIso a b).hom.app C ≫
        eqToHom (congrArg (fun ψ => (extensionOfScalarsComplex.{u, u, u} ψ).obj C) h.symm) := by
  subst h
  simp only [eqToIso_refl, Iso.trans_refl, eqToHom_refl]
  exact derivedExtensionScalarsCompIso_hom_app_comp_comparison a b C

/-- **The transported composition isomorphism, read backwards against the untransported one.**
At an object `C` of the derived category of `R`-modules, the transport of
`derivedExtensionScalarsCompIso` along an equation `φ = b ∘ a`, read backwards and followed by the
untransported isomorphism, is the transport alone.

A chase that meets the transported merge on one side and — because that is what the characterizing
equation produces — the untransported one on the other cancels the two with this and keeps only
the transport.  Proved by substituting the equation, after which both sides are identities. -/
theorem compIso_eqToIso_inv_app_comp_compIso_hom_app
    (a : R →+* S) (b : S →+* T) (φ : R →+* T) (h : φ = b.comp a)
    (C : DerivedCategory (ModuleCat.{u} R)) :
    (derivedExtensionScalarsCompIso a b ≪≫
            eqToIso (congrArg
              (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor) h.symm)).inv.app C ≫
        (derivedExtensionScalarsCompIso a b).hom.app C =
      eqToHom (congrArg
        (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj C) h) := by
  subst h
  simp only [eqToIso_refl, Iso.trans_refl, eqToHom_refl, Iso.inv_hom_id_app]

end StacksDraft.DerivedExtensionScalarsComp

namespace Stacks.ModuleSkyscraper

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)

/-- **The underived merge of the two extensions of scalars along the germ maps is Mathlib's
composition isomorphism.**  `extendScalarsStalkComp` is `ModuleCat.extendScalarsComp` at the two
germ maps, read backwards and transported along `stalkMap_hom_comp`.

This is `StacksDraft.DerivedExtensionScalarsComp.leftAdjointCompIso_restrictScalarsComp'` at the
germ maps; `extendScalarsStalkComp` is by definition the left-adjoint composition isomorphism of
`restrictScalarsStalkComp`, which is `ModuleCat.restrictScalarsComp'` at `stalkMap_hom_comp`. -/
theorem extendScalarsStalkComp_eq :
    extendScalarsStalkComp f g x =
      (ModuleCat.extendScalarsComp.{u} (g.stalkMap (f x)).hom (f.stalkMap x).hom).symm ≪≫
        eqToIso (congrArg ModuleCat.extendScalars.{u} (stalkMap_hom_comp f g x).symm) :=
  StacksDraft.DerivedExtensionScalarsComp.leftAdjointCompIso_restrictScalarsComp'
    _ _ _ (stalkMap_hom_comp f g x)

/-- `extendScalarsStalkComp_eq` at a module: the merge of the two extensions of scalars along the
germ maps, at an `𝒪_{Z, g (f x)}`-module. -/
theorem extendScalarsStalkComp_hom_app (M : ModuleCat.{u} (ToType (Z.presheaf.stalk (g (f x))))) :
    (extendScalarsStalkComp f g x).hom.app M =
      (ModuleCat.extendScalarsComp.{u} (g.stalkMap (f x)).hom (f.stalkMap x).hom).inv.app M ≫
        eqToHom (congrArg (fun ψ => (ModuleCat.extendScalars.{u} ψ).obj M)
          (stalkMap_hom_comp f g x).symm) := by
  rw [extendScalarsStalkComp_eq]
  simp [eqToHom_app]

/-- **Stacks 0098's composition compatibility, read backwards.**  For an `𝒪_Z`-module `N`, the
stalk at `x` of the pullback-composition isomorphism of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` is the two stalk formulas of Stacks 0098 read
backwards — for `f` at `x` on `g^*N`, then for `g` at `f x` with scalars extended along the germ
map of `f` — followed by the merge `extendScalarsStalkComp` of the two extensions of scalars and
then the stalk formula for `f ≫ g`.

The statement composes with the stalk formula for `f ≫ g` rather than with its inverse on the
other side; see the implementation notes.  The proof is `pullbackStalkIso_comp_app` followed by
three cancellations. -/
theorem modulesStalkFunctor_map_pullbackComp_hom_app (N : Z.Modules) :
    (modulesStalkFunctor X x).map ((Scheme.Modules.pullbackComp f g).hom.app N) =
      ((pullbackStalkIso f x).inv.app ((Scheme.Modules.pullback g).obj N) ≫
          (ModuleCat.extendScalars.{u} (f.stalkMap x).hom).map
            ((pullbackStalkIso g (f x)).inv.app N) ≫
          (extendScalarsStalkComp f g x).hom.app ((modulesStalkFunctor Z (g (f x))).obj N)) ≫
        (pullbackStalkIso (f ≫ g) x).hom.app N := by
  have hc : (ModuleCat.extendScalars.{u} (f.stalkMap x).hom).map
            ((pullbackStalkIso g (f x)).inv.app N) ≫
          (ModuleCat.extendScalars.{u} (f.stalkMap x).hom).map
            ((pullbackStalkIso g (f x)).hom.app N) ≫
          (pullbackStalkIso f x).hom.app ((Scheme.Modules.pullback g).obj N) ≫
            (modulesStalkFunctor X x).map ((Scheme.Modules.pullbackComp f g).hom.app N) =
        (pullbackStalkIso f x).hom.app ((Scheme.Modules.pullback g).obj N) ≫
          (modulesStalkFunctor X x).map ((Scheme.Modules.pullbackComp f g).hom.app N) :=
      Iso.inv_hom_id_assoc ((ModuleCat.extendScalars.{u} (f.stalkMap x).hom).mapIso
        ((pullbackStalkIso g (f x)).app N)) _
  rw [pullbackStalkIso_comp_app f g x N, Category.assoc, Category.assoc,
    Iso.hom_inv_id_app_assoc, hc, Iso.inv_hom_id_app_assoc]

/-- `modulesStalkFunctor_map_pullbackComp_hom_app` with the stalk formula for `f ≫ g` moved to the
other side as its inverse.  This is the form the derived chase consumes: it rewrites the stalk
formula for `f ≫ g`, read backwards, in terms of the two factors.

Obtained in term mode, where the conversion between the two spellings of the point `(f ≫ g) x`
runs at default transparency. -/
theorem pullbackStalkIso_comp_inv_app (N : Z.Modules) :
    (modulesStalkFunctor X x).map ((Scheme.Modules.pullbackComp f g).hom.app N) ≫
        (pullbackStalkIso (f ≫ g) x).inv.app N =
      (pullbackStalkIso f x).inv.app ((Scheme.Modules.pullback g).obj N) ≫
        (ModuleCat.extendScalars.{u} (f.stalkMap x).hom).map
          ((pullbackStalkIso g (f x)).inv.app N) ≫
        (extendScalarsStalkComp f g x).hom.app ((modulesStalkFunctor Z (g (f x))).obj N) :=
  (Iso.comp_inv_eq ((pullbackStalkIso (f ≫ g) x).app N)).2
    (modulesStalkFunctor_map_pullbackComp_hom_app f g x N)

end Stacks.ModuleSkyscraper

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)

/-- **The merged extension-of-scalars tail of the iterated derived stalk.**  At a cochain complex
`C` of `𝒪_{Z, g (f x)}`-modules, the merge `derivedStalkExtensionCompIso` of the two derived
extensions of scalars along the germ maps, followed by the comparison of derived with degreewise
extension of scalars along the germ map of `f ≫ g`, is the comparison for `g` at `f x`, then the
comparison for `f` at `x`, then the degreewise merge `extensionScalarsComplexCompIso`.

This is the fourth step of the assembly of the hypothesis of
`derivedPullbackStalkIso_comp_of_kFlat`: it is what replaces the two extension-of-scalars tails of
the two-step stalk computation by the single tail that the one-step computation for `f ≫ g`
carries.  It is
`StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso_eqToIso_comp_comparison`
at the two germ maps and `Stacks.ModuleSkyscraper.stalkMap_hom_comp`. -/
theorem derivedStalkExtensionCompIso_hom_app_comp_comparison
    (C : CochainComplex (ModuleCat.{u} (ToType (Z.presheaf.stalk (g (f x))))) ℤ) :
    (derivedStalkExtensionCompIso f g x).hom.app (DerivedCategory.Q.obj C) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).comparison.app C =
      (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} (g.stalkMap (f x)).hom).comparison.app C) ≫
        (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).comparison.app
          (((ModuleCat.extendScalars (g.stalkMap (f x)).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C) ≫
        (StacksDraft.DerivedExtensionScalarsComp.extensionScalarsComplexCompIso
          (g.stalkMap (f x)).hom (f.stalkMap x).hom).hom.app C ≫
        eqToHom (congrArg (fun ψ => (extensionOfScalarsComplex.{u, u, u} ψ).obj C)
          (Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x).symm) :=
  StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso_eqToIso_comp_comparison
    _ _ _ (Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x) C

/-- **The transported merge, read backwards against the untransported one.**  At an object `C` of
the derived category of `𝒪_{Z, g (f x)}`-modules, `derivedStalkExtensionCompIso` read backwards,
followed by the untransported composition isomorphism
`StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso` of the two germ maps, is
the transport along `Stacks.ModuleSkyscraper.stalkMap_hom_comp`.

This is what lets a chase that meets the transported merge on one side and the untransported one
on the other — the untransported one is what the characterizing equation produces — cancel the
two and keep only the transport.  Stated here, in the module that owns the transport, so that no
consumer converts between the two spellings of the germ map of a composite.

This is `StacksDraft.DerivedExtensionScalarsComp.compIso_eqToIso_inv_app_comp_compIso_hom_app` at
the two germ maps and `Stacks.ModuleSkyscraper.stalkMap_hom_comp`. -/
theorem derivedStalkExtensionCompIso_inv_app_comp_compIso_hom_app
    (C : DerivedCategory (ModuleCat.{u} (ToType (Z.presheaf.stalk (g (f x)))))) :
    (derivedStalkExtensionCompIso f g x).inv.app C ≫
        (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso
          (g.stalkMap (f x)).hom (f.stalkMap x).hom).hom.app C =
      eqToHom (congrArg (fun φ => (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj C)
        (Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x)) :=
  StacksDraft.DerivedExtensionScalarsComp.compIso_eqToIso_inv_app_comp_compIso_hom_app
    _ _ _ (Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x) C

/-- **The untransported merge, read as the transported one.**
`derivedStalkExtensionCompIso_inv_app_comp_compIso_hom_app` with the inverse moved to the other
side: the untransported composition isomorphism of the two germ maps is the transported merge
followed by the transport along `Stacks.ModuleSkyscraper.stalkMap_hom_comp`.

This is the direction a chase that opens with the untransported merge on one side and with the
transported one on the other needs.  Stated here, in the module that owns the transport, because
the target of the transported merge is spelled at `(f ≫ g).stalkMap x` and that is not
interchangeable with the germ map at `g (f x)` at the transparency `rw` type-checks its motives
at: a consumer that moved the inverse itself would be rewriting an ill-typed motive. -/
theorem derivedExtensionScalarsCompIso_hom_app_eq
    (C : DerivedCategory (ModuleCat.{u} (ToType (Z.presheaf.stalk (g (f x)))))) :
    (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso
          (g.stalkMap (f x)).hom (f.stalkMap x).hom).hom.app C =
      (derivedStalkExtensionCompIso f g x).hom.app C ≫
        eqToHom (congrArg (fun φ => (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj C)
          (Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x)) :=
  (CategoryTheory.Iso.inv_comp_eq ((derivedStalkExtensionCompIso f g x).app C)).1
    (derivedStalkExtensionCompIso_inv_app_comp_compIso_hom_app f g x C)

end AlgebraicGeometry

end
