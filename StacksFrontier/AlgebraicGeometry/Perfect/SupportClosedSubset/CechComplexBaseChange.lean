module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechTermBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ExtendedCechComplexComparison

/-!
# Base change of the extended alternating Čech complex along an open immersion

Let `X` be a scheme, `f₁, …, f_c ∈ Γ(X, 𝒪_X)`, `ℱ` an `𝒪_X`-module, `g : X' ⟶ X` an open
immersion and `f'ᵢ` the pullback of `fᵢ` along `g`.  [Stacks, Tag 0G7U] asserts, among other
things, the identification `(ℱ')^• = g^*ℱ^•` of the extended alternating Čech complex of the
pulled-back equations with the pullback of the extended alternating Čech complex.  This file
proves it for `g` an open immersion: the restriction along `g` of a complex satisfying the
specification of [Stacks, Tag 0G7I] for `f` and `ℱ` *satisfies that specification* for `f'` and
`g^*ℱ`.

`CechTermBaseChange` supplies the degreewise comparison and `CechTermBaseChangeSections` what it
does to a section.  What this file adds is the two differential clauses, which is the whole of
the content: the specification pins the differentials down by their effect on sections, and the
comparison is a restriction map there, so both differentials become the same ordered Čech
differential after the transport `inter_image` of the principal intersections.

## Main definitions

* `restrictComplex`, `restrictZeroIso`, `restrictTermIso`, `restrictSectionsIso`: the restricted
  complex and the three identifications the specification of Tag 0G7I asks for.
* `restrictData`: **the restricted complex as an inhabitant of the specification** for the
  restricted equations and `g^*ℱ`.
* `restrictComplexIso`: the resulting canonical isomorphism with any other inhabitant of the
  specification for the restricted equations — in particular with the complex Tag 0G7I
  constructs — through `Stacks.Perfect.CechComplexComparison.comparisonIso`.

## Main results

* `restrictSectionsIso_eq`: the sectionwise identification of the restricted complex is that of
  the complex on the image open, transported along `inter_image`.
* `ordD_transport`: that transport intertwines the two ordered Čech differentials.
* `restrictSectionsIso_differential_zero`, `restrictSectionsIso_differential_succ`: **the two
  differential clauses**, the content of the identification.

## What is *not* here

This is the identification of the *complexes* only.  The class map of [Stacks, Tag 0G7Q] and the
morphism `ℱ ⟶ i_*ℋ^c_Z(ℱ)` of [Stacks, Tag 0G7T] are not carried across: beyond the
identification above that needs the compatibility of the comparison of [Stacks, Tag 0G7L] with
the excision isomorphism
`Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso`, which is not proved.
Everything here is for an **open immersion**; for a general morphism the termwise comparison it
rests on is not available.

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

variable {X X' : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (g : X' ⟶ X) [IsOpenImmersion g]
  {F : X.Modules} (D : ExtendedAlternatingCechData f F)

/-- The restriction along `g` of a complex satisfying the specification of
[Stacks, Tag 0G7I]. -/
public def restrictComplex : CochainComplex X'.Modules ℕ :=
  ((Scheme.Modules.restrictFunctor g).mapHomologicalComplex (ComplexShape.up ℕ)).obj D.complex

/-- Degree `0` of the restricted complex is the restricted coefficient module. -/
public def restrictZeroIso :
    (restrictComplex f g D).X 0 ≅ (Scheme.Modules.restrictFunctor g).obj F :=
  (Scheme.Modules.restrictFunctor g).mapIso D.zeroIso

/-- Degree `p + 1` of the restricted complex is the product of the direct images of the
restrictions of `F|_W` to the principal intersections of the restricted equations. -/
public def restrictTermIso (p : ℕ) :
    (restrictComplex f g D).X (p + 1) ≅
      ∏ᶜ fun s : CechCochains.OrdIndex (I := Fin c) p =>
        restrictedModule (fun j => g.appTop (f j))
          ((Scheme.Modules.restrictFunctor g).obj F) p s :=
  (Scheme.Modules.restrictFunctor g).mapIso (D.termIso p) ≪≫ restrictProdTermIso f g F p

/-- On every open of `X'`, the degree-`(p + 1)` sections of the restricted complex are the
ordered Čech `p`-cochains of the restricted equations. -/
public def restrictSectionsIso (p : ℕ) (V : X'.Opens) :
    Γ((restrictComplex f g D).X (p + 1), V) ≃+
      CechCochains.OrdCochain (fun i => V ⊓ X'.basicOpen (g.appTop (f i)))
        (Scheme.Modules.presheaf ((Scheme.Modules.restrictFunctor g).obj F)) p :=
  (abIsoEquiv ((ev X' V).mapIso (restrictTermIso f g D p))).trans
    (secIso (fun j => g.appTop (f j)) ((Scheme.Modules.restrictFunctor g).obj F) p V)

/-- The sectionwise identification of the restricted complex is the componentwise one. -/
public theorem restrictSectionsIso_compat (p : ℕ) (V : X'.Opens)
    (x : Γ((restrictComplex f g D).X (p + 1), V))
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    restrictSectionsIso f g D p V x s =
      restrictedModuleSection (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F) p s V
        (((restrictTermIso f g D p).hom ≫ Pi.π _ s).app V x) := rfl

/-- The sectionwise identification of the restricted complex is the sectionwise identification
of the complex on the image open, transported along `inter_image`. -/
public theorem restrictSectionsIso_eq (p : ℕ) (V : X'.Opens)
    (y : Γ(D.complex.X (p + 1), g ''ᵁ V))
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    restrictSectionsIso f g D p V y s =
      F.presheaf.map (eqToHom (inter_image f g V p s)).op
        (D.sectionsIso p (g ''ᵁ V) y s) := by
  refine Eq.trans (secIso_restrictProdTermIso f g F p V
    ((D.termIso p).hom.app (g ''ᵁ V) y) s) ?_
  exact map_congr F (eqToHom (inter_image f g V p s))
    ((secIso_apply f F p (g ''ᵁ V) _ s).trans
      (D.sectionsIso_compat p (g ''ᵁ V) y s).symm)

/-- A restriction map of a module commutes with finite sums of sections. -/
public theorem map_sum_apply {Z : Scheme.{u}} (N : Z.Modules) {A B : Z.Opens} (φ : B ⟶ A)
    {ι : Type} (σ : Finset ι) (y : ι → Γ(N, A)) :
    N.presheaf.map φ.op (∑ i ∈ σ, y i) = ∑ i ∈ σ, N.presheaf.map φ.op (y i) :=
  map_sum _ y σ

/-- A restriction map of a module commutes with integer scaling of sections. -/
public theorem map_zsmul_apply {Z : Scheme.{u}} (N : Z.Modules) {A B : Z.Opens} (φ : B ⟶ A)
    (n : ℤ) (y : Γ(N, A)) :
    N.presheaf.map φ.op (n • y) = n • N.presheaf.map φ.op y :=
  map_zsmul _ n y

/-- Integer scaling of equal sections. -/
public theorem zsmul_congr {Z : Scheme.{u}} (N : Z.Modules) {A : Z.Opens} (n : ℤ)
    {y y' : Γ(N, A)} (e : y = y') : n • y = n • y' :=
  congrArg (fun w => n • w) e

/-- The ordered Čech restriction map applied to equal sections. -/
public theorem restr_congr {Z : Scheme.{u}} (N : Z.Modules) {A B : Z.Opens} (h : B ≤ A)
    {y y' : Γ(N, A)} (e : y = y') :
    CechCochains.restr (Scheme.Modules.presheaf N) h y =
      CechCochains.restr (Scheme.Modules.presheaf N) h y' :=
  congrArg (fun w => CechCochains.restr (Scheme.Modules.presheaf N) h w) e

/-- The transport along `inter_image` intertwines the ordered Čech restriction maps. -/
public theorem restr_transport (p : ℕ) (V : X'.Opens)
    {s : CechCochains.OrdIndex (I := Fin c) p}
    {t : CechCochains.OrdIndex (I := Fin c) (p + 1)}
    (hst : CechCochains.inter
        (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) t.1 ≤
      CechCochains.inter (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) s.1)
    (hst' : CechCochains.inter (fun i => (g ''ᵁ V) ⊓ X.basicOpen (f i)) t.1 ≤
      CechCochains.inter (fun i => (g ''ᵁ V) ⊓ X.basicOpen (f i)) s.1)
    (y : Γ(F, CechCochains.inter (fun i => (g ''ᵁ V) ⊓ X.basicOpen (f i)) s.1)) :
    CechCochains.restr
        (Scheme.Modules.presheaf ((Scheme.Modules.restrictFunctor g).obj F)) hst
        (F.presheaf.map (eqToHom (inter_image f g V p s)).op y) =
      F.presheaf.map (eqToHom (inter_image f g V (p + 1) t)).op
        (CechCochains.restr (Scheme.Modules.presheaf F) hst' y) := by
  have himg : g ''ᵁ (CechCochains.inter
        (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) t.1) ≤
      g ''ᵁ (CechCochains.inter
        (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) s.1) := by
    rw [inter_image, inter_image]
    exact hst'
  refine Eq.trans (restr_eq ((Scheme.Modules.restrictFunctor g).obj F) hst _) ?_
  refine Eq.trans (restrictFunctor_presheaf_map g F (homOfLE hst) (homOfLE himg) _) ?_
  refine Eq.trans ?_ (map_congr F (eqToHom (inter_image f g V (p + 1) t))
    (restr_eq F hst' y)).symm
  exact collapse2_eq F _ _ _ _ y

/-- **The transport along `inter_image` intertwines the two ordered Čech differentials.** -/
public theorem ordD_transport (p : ℕ) (V : X'.Opens)
    (cc : CechCochains.OrdCochain (fun i => (g ''ᵁ V) ⊓ X.basicOpen (f i))
      (Scheme.Modules.presheaf F) p)
    (cc' : CechCochains.OrdCochain (fun i => V ⊓ X'.basicOpen (g.appTop (f i)))
      (Scheme.Modules.presheaf ((Scheme.Modules.restrictFunctor g).obj F)) p)
    (hcc : ∀ s, cc' s = F.presheaf.map (eqToHom (inter_image f g V p s)).op (cc s))
    (t : CechCochains.OrdIndex (I := Fin c) (p + 1)) :
    CechCochains.ordD (fun i => V ⊓ X'.basicOpen (g.appTop (f i)))
        (Scheme.Modules.presheaf ((Scheme.Modules.restrictFunctor g).obj F)) p cc' t =
      F.presheaf.map (eqToHom (inter_image f g V (p + 1) t)).op
        (CechCochains.ordD (fun i => (g ''ᵁ V) ⊓ X.basicOpen (f i))
          (Scheme.Modules.presheaf F) p cc t) := by
  refine Eq.trans (ordD_apply (fun j => g.appTop (f j))
    ((Scheme.Modules.restrictFunctor g).obj F) V p cc' t) ?_
  refine Eq.trans ?_ (map_congr F (eqToHom (inter_image f g V (p + 1) t))
    (ordD_apply f F (g ''ᵁ V) p cc t)).symm
  refine Eq.trans ?_ (map_sum_apply F (eqToHom (inter_image f g V (p + 1) t))
    Finset.univ _).symm
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Eq.trans ?_ (map_zsmul_apply F (eqToHom (inter_image f g V (p + 1) t)) _ _).symm
  refine zsmul_congr F _ ?_
  let s : CechCochains.OrdIndex (I := Fin c) p :=
    ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩
  have h := CechCochains.inter_le_omit (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) t.1 j
  have h' := CechCochains.inter_le_omit (fun i => (g ''ᵁ V) ⊓ X.basicOpen (f i)) t.1 j
  exact (restr_congr _ h (hcc s)).trans (restr_transport f g p V (s := s) (t := t) h h' (cc s))

/-- **The augmentation of the restricted complex is the restriction map.** -/
public theorem restrictSectionsIso_differential_zero (V : X'.Opens)
    (x : Γ((restrictComplex f g D).X 0, V)) (s : CechCochains.OrdIndex (I := Fin c) 0) :
    restrictSectionsIso f g D 0 V (((restrictComplex f g D).d 0 1).app V x) s =
      (Scheme.Modules.presheaf ((Scheme.Modules.restrictFunctor g).obj F)).map
        (homOfLE (show CechCochains.inter
            (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) s.1 ≤ V from
          (iInf_le _ (0 : Fin 1)).trans inf_le_left)).op
        ((restrictZeroIso f g D).hom.app V x) := by
  have h0 : CechCochains.inter (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) s.1 ≤ V :=
    (iInf_le _ (0 : Fin 1)).trans inf_le_left
  refine Eq.trans (restrictSectionsIso_eq f g D 0 V _ s) ?_
  refine Eq.trans (map_congr F (eqToHom (inter_image f g V 0 s))
    (D.differential_zero (g ''ᵁ V) x s)) ?_
  refine Eq.trans ?_ (restrictFunctor_presheaf_map g F (homOfLE h0)
    (homOfLE (Scheme.Hom.image_mono g h0)) ((restrictZeroIso f g D).hom.app V x)).symm
  exact collapse2 F _ _ _ _

/-- **In positive degrees the differential of the restricted complex is the signed alternating
restriction map.** -/
public theorem restrictSectionsIso_differential_succ (p : ℕ) (V : X'.Opens)
    (x : Γ((restrictComplex f g D).X (p + 1), V)) :
    restrictSectionsIso f g D (p + 1) V
        (((restrictComplex f g D).d (p + 1) (p + 2)).app V x) =
      CechCochains.ordD (fun i => V ⊓ X'.basicOpen (g.appTop (f i)))
        (Scheme.Modules.presheaf ((Scheme.Modules.restrictFunctor g).obj F)) p
        (restrictSectionsIso f g D p V x) := by
  funext t
  refine Eq.trans (restrictSectionsIso_eq f g D (p + 1) V _ t) ?_
  refine Eq.trans (map_congr F (eqToHom (inter_image f g V (p + 1) t))
    (congrFun (D.differential_succ p (g ''ᵁ V) x) t)) ?_
  exact (ordD_transport f g p V (D.sectionsIso p (g ''ᵁ V) x)
    (restrictSectionsIso f g D p V x) (restrictSectionsIso_eq f g D p V x) t).symm

/-- **The restriction to an open of a complex satisfying the specification of
[Stacks, Tag 0G7I]** satisfies the specification for the restricted equations and the restricted
coefficient module.  This is the identification `(ℱ')^• = g^*ℱ^•` of [Stacks, Tag 0G7U] for `g`
an open immersion, in the form the specification gives it. -/
public def restrictData : ExtendedAlternatingCechData (fun j => g.appTop (f j))
    ((Scheme.Modules.restrictFunctor g).obj F) where
  complex := restrictComplex f g D
  zeroIso := restrictZeroIso f g D
  termIso := restrictTermIso f g D
  sectionsIso := restrictSectionsIso f g D
  sectionsIso_compat := restrictSectionsIso_compat f g D
  differential_zero := restrictSectionsIso_differential_zero f g D
  differential_succ := restrictSectionsIso_differential_succ f g D

/-- **The identification of the two extended alternating Čech complexes of [Stacks, Tag 0G7U]
along an open immersion.**  The restriction along `g` of a complex satisfying the specification
of [Stacks, Tag 0G7I] for `f` and `ℱ` is canonically isomorphic to any complex satisfying it for
the restricted equations and `g^*ℱ` — in particular to the one `Tag 0G7I` constructs. -/
public def restrictComplexIso
    (D' : ExtendedAlternatingCechData (fun j => g.appTop (f j))
      ((Scheme.Modules.restrictFunctor g).obj F)) :
    restrictComplex f g D ≅ D'.complex :=
  CechComplexComparison.comparisonIso (restrictData f g D) D'

end Stacks.Perfect.PushforwardRestrict

end
