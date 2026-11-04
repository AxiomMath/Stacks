module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechTermBaseChange

/-!
# The termwise comparison of the extended alternating Čech complex, on sections

Let `X` be a scheme, `f₁, …, f_c ∈ Γ(X, 𝒪_X)`, `g : X' ⟶ X` an open immersion and `f'ᵢ` the
pullback of `fᵢ` along `g`.  `CechTermBaseChange` identifies the restriction along `g` of the term
`F_{i₀…i_p} = (U_{i₀…i_p} → X)_*(F|_{U_{i₀…i_p}})` of the extended alternating Čech complex of
[Stacks, Tag 0G7I] with the term `(g^*F)'_{i₀…i_p}` of the complex of the restricted equations.
This file computes what that identification does to a section, which is what the comparison of
the *complexes* needs: the differentials of Tag 0G7I are specified by their effect on sections,
so the comparison commutes with them exactly when it is a restriction map on sections.

## Main results

* `inter_image`: the image in `X` of the principal intersection `V ∩ U'_{i₀…i_p}` of the
  restricted equations is the principal intersection `g(V) ∩ U_{i₀…i_p}` of the equations.
* `restrictedModuleSection_restrictRestrictedModuleIso`: **the termwise comparison on
  sections.**  Reading the image of a section under the comparison is restricting the section
  along `inter_image`.

## Implementation notes

The sectionwise identification `Stacks.Perfect.ExtendedAlternatingCech.restrictedModuleSection`
of a term is the generic reading `Stacks.Perfect.PushforwardRestrict.restrictedSection` of a
section of a direct image of a restriction, transported from `U_{i₀…i_p} ∩ V` to the principal
intersection by `himage`; so the content of the comparison is the generic
`restrictedSection_restrictedRestrictIso`, and what is left is the bookkeeping of the three
transports, all of which happens in the `Γ(F, -)` spelling where a composite of restriction maps
collapses for free.

Both vocabularies of Tag 0G7I — `AlgebraicGeometry.ExtendedAlternatingCech` and
`Stacks.Perfect.ExtendedAlternatingCech` — define `equationsOpen` and `restrictedModule` by the
same body, so the two are definitionally equal but not syntactically so; mixing them makes every
unifier call unfold both, which exhausts the recursion depth.  One spelling is therefore pinned
throughout, the `Stacks.Perfect` one, which is the one the complex data of
`GlobalEquationsComplexData` is stated in.  The one place the other vocabulary is still needed is
the compatibility of the principal intersections with inverse images, which
`AlgebraicGeometry.ExtendedAlternatingCech.equationsOpen_pullback` proves and which is used
directly at the few sites that want it in the `Stacks.Perfect` spelling.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.PushforwardRestrict

variable {X X' : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (g : X' ⟶ X)
  [IsOpenImmersion g]

/-- A restriction map applied to equal sections. -/
public theorem map_congr {Z : Scheme.{u}} (N : Z.Modules) {A B : Z.Opens} (φ : B ⟶ A)
    {y y' : Γ(N, A)} (h : y = y') :
    N.presheaf.map φ.op y = N.presheaf.map φ.op y' :=
  congrArg (fun w => N.presheaf.map φ.op w) h

/-- A restriction map of a restricted module is a restriction map of the module. -/
public theorem restrictFunctor_presheaf_map {Z Z' : Scheme.{u}} (l : Z' ⟶ Z)
    [IsOpenImmersion l] (F : Z.Modules) {A B : Z'.Opens} (φ : B ⟶ A) (h : l ''ᵁ B ⟶ l ''ᵁ A)
    (y : Γ((Scheme.Modules.restrictFunctor l).obj F, A)) :
    ((Scheme.Modules.restrictFunctor l).obj F).presheaf.map φ.op y =
      F.presheaf.map h.op y := by
  rw [Scheme.Modules.restrict_map]
  exact map_eq_apply F _ h y

/-- The image in `X` of the principal intersection of the restricted equations is the principal
intersection of the equations. -/
public theorem inter_image (V : X'.Opens) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    g ''ᵁ (CechCochains.inter
        (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) s.1) =
      CechCochains.inter (fun i => (g ''ᵁ V) ⊓ X.basicOpen (f i)) s.1 :=
  ((congrArg (fun B : X'.Opens => g ''ᵁ B)
        (himage (fun j => g.appTop (f j)) p s V).symm).trans
      (restrictImage_eq (equationsOpen f p s) g
        (AlgebraicGeometry.ExtendedAlternatingCech.equationsOpen_pullback g f p s) V)).trans
    (himage f p s (g ''ᵁ V))

/-- The sectionwise identification of a term of the complex is the generic reading of the
section, transported to the principal intersection. -/
public theorem restrictedModuleSection_eq_restrictedSection (F : X.Modules) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) (V : X.Opens)
    (z : Γ(restrictedModule f F p s, V)) :
    restrictedModuleSection f F p s V z =
      F.presheaf.map (eqToHom (himage f p s V).symm).op
        (restrictedSection (equationsOpen f p s) F V z) :=
  restrictedModuleSection_apply f F p s V z

/-- **The termwise comparison of [Stacks, Tag 0G7U] along an open immersion, on sections.**
Reading the image of a section under the comparison is restricting the section along the
equality `inter_image` of principal intersections. -/
public theorem restrictedModuleSection_restrictRestrictedModuleIso (F : X.Modules) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) (V : X'.Opens)
    (z : Γ(restrictedModule f F p s, g ''ᵁ V)) :
    restrictedModuleSection (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F) p s V
        ((restrictRestrictedModuleIso f g F p s).hom.app V z) =
      F.presheaf.map (eqToHom (inter_image f g V p s)).op
        (restrictedModuleSection f F p s (g ''ᵁ V) z) := by
  have key := restrictedSection_restrictedRestrictIso (equationsOpen f p s) g F V
    (AlgebraicGeometry.ExtendedAlternatingCech.equationsOpen_pullback g f p s) z
  refine Eq.trans (restrictedModuleSection_eq_restrictedSection (fun j => g.appTop (f j))
    ((Scheme.Modules.restrictFunctor g).obj F) p s V _) ?_
  refine Eq.trans (map_congr ((Scheme.Modules.restrictFunctor g).obj F)
    (eqToHom (himage (fun j => g.appTop (f j)) p s V).symm) key) ?_
  refine Eq.trans (restrictFunctor_presheaf_map g F
    (eqToHom (himage (fun j => g.appTop (f j)) p s V).symm)
    (eqToHom (congrArg (fun C : X'.Opens => g ''ᵁ C)
      (himage (fun j => g.appTop (f j)) p s V).symm)) _) ?_
  refine Eq.trans ?_ (map_congr F (eqToHom (inter_image f g V p s))
    (restrictedModuleSection_eq_restrictedSection f F p s (g ''ᵁ V) z)).symm
  exact collapse2_eq F _ _ _ _ _

/-- **The degreewise comparison of [Stacks, Tag 0G7U] along an open immersion, on sections.**
In each component it is the restriction along `inter_image`. -/
public theorem secIso_restrictProdTermIso (F : X.Modules) (p : ℕ) (V : X'.Opens)
    (x : Γ(prodTerm f F p, g ''ᵁ V)) (s : CechCochains.OrdIndex (I := Fin c) p) :
    secIso (fun j => g.appTop (f j)) ((Scheme.Modules.restrictFunctor g).obj F) p V
        ((restrictProdTermIso f g F p).hom.app V x) s =
      F.presheaf.map (eqToHom (inter_image f g V p s)).op (secIso f F p (g ''ᵁ V) x s) := by
  have hπ := congrArg (fun ψ : (Scheme.Modules.restrictFunctor g).obj (prodTerm f F p) ⟶
      restrictedModule (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F) p s => ψ.app V x)
    (restrictProdTermIso_hom_comp_π f g F p s)
  refine Eq.trans (secIso_apply (fun j => g.appTop (f j))
    ((Scheme.Modules.restrictFunctor g).obj F) p V _ s) ?_
  refine Eq.trans (congrArg (restrictedModuleSection (fun j => g.appTop (f j))
    ((Scheme.Modules.restrictFunctor g).obj F) p s V) hπ) ?_
  exact restrictedModuleSection_restrictRestrictedModuleIso f g F p s V _

end Stacks.Perfect.PushforwardRestrict

end
