module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale sheaves on the spectrum of a separably closed field

Let `k` be a separably closed field. Every scheme étale over `Spec k` is covered by its
`k`-rational points, because the residue field at a point of such a scheme is a separable
algebraic extension of `k`, hence `k` itself. In the language of sites: the final object
`Spec k` of the small étale site of `Spec k`, seen as a functor from the one-point category,
exhibits the one-point category with its trivial topology as a dense subsite. So sheaves on the
small étale site of `Spec k` are the same thing as objects of the coefficient category, the
equivalence being evaluation at the final object, that is, global sections.

## Main results

* `Stacks.EtaleCohomology.coverByImage_mem_smallEtaleTopology_of_isSepClosed` — over a
  separably closed field every object of the small étale site is covered by morphisms out of the
  final object.
* `Stacks.EtaleCohomology.isDenseSubsite_fromPUnit_of_isSepClosed` — hence the final object,
  as a functor from the one-point category with its trivial topology, is a dense subsite.
* `Stacks.EtaleCohomology.isEquivalence_sheafSections_final_of_isSepClosed` — evaluation at the
  final object is an equivalence from sheaves to the coefficient category.
* `Stacks.EtaleCohomology.isEquivalence_globalSections_of_isSepClosed` — over a separably
  closed field, global sections `Sheaf.Γ` is an equivalence from sheaves on the small étale site
  to the coefficient category.
* `isEquivalence_sheafPushforwardContinuous_smallEtaleBaseChange_of_isSepClosed` — for an
  extension `K/k` of separably closed fields, direct image along `Spec K ⟶ Spec k` is an
  equivalence, with coefficients in any category with limits.
* `Stacks.EtaleCohomology.isEquivalence_etaleAbelianDirectImage_of_isSepClosed` and
  `Stacks.EtaleCohomology.isEquivalence_etaleAbelianInverseImage_of_isSepClosed` — for an
  extension `K/k` of separably closed fields, direct and inverse image of abelian sheaves along
  `Spec K ⟶ Spec k` are equivalences.

## Implementation notes

The one-point category is `Discrete PUnit` with the trivial (bottom) topology, and the functor is
`CategoryTheory.Functor.fromPUnit` of the final object `Scheme.Etale.mk (𝟙 (Spec k))`. Mathlib's
comparison lemma `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` then identifies the sheaves;
sheaves for the bottom topology are presheaves (`CategoryTheory.sheafBotEquivalence`), and a
presheaf on the one-point category is an object of the coefficient category.

For an extension `K/k`, direct image along `g : Spec K ⟶ Spec k` is restriction along base
change, and base change carries the final object to a final object, so global sections over
`Spec k` of a direct image are global sections over `Spec K`. Both global sections functors being
equivalences, so is the direct image, and hence its left adjoint, the inverse image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u v

namespace Stacks.EtaleCohomology

section SeparablyClosedField

variable (k : Type u) [Field k] [IsSepClosed k]

/-- **Over a separably closed field every étale scheme is covered by its rational points.** The
sieve of morphisms out of the final object `Spec k` of the small étale site of `Spec k` covers
every object. -/
public theorem coverByImage_mem_smallEtaleTopology_of_isSepClosed
    (U : (Spec (.of k)).Etale) :
    Sieve.coverByImage (Functor.fromPUnit.{0} (Scheme.Etale.mk (𝟙 (Spec (.of k))))) U ∈
      (Spec (.of k)).smallEtaleTopology U := by
  rw [mem_smallEtaleTopology_iff]
  intro x
  obtain ⟨l, hl, hlx⟩ := Scheme.exists_fac_of_etale_of_isSepClosed U.hom
    (𝟙 (Spec (.of k))) x (Subsingleton.elim (α := Spec (.of k)) _ _)
  let g : Scheme.Etale.mk (𝟙 (Spec (.of k))) ⟶ U := MorphismProperty.Over.homMk l hl trivial
  exact ⟨Scheme.Etale.mk (𝟙 (Spec (.of k))), g,
    Presieve.in_coverByImage (Functor.fromPUnit.{0} (Scheme.Etale.mk (𝟙 (Spec (.of k)))))
      (Y := ⟨⟨⟩⟩) g,
    ⟨(default : Spec (.of k)), hlx⟩⟩

/-- The final object of the small étale site of `Spec k`, as a functor from the one-point
category, exhibits the one-point category with its trivial topology as a dense subsite of the
small étale site of `Spec k`. -/
public instance isDenseSubsite_fromPUnit_of_isSepClosed :
    (Functor.fromPUnit.{0} (Scheme.Etale.mk (𝟙 (Spec (.of k))))).IsDenseSubsite
      (⊥ : GrothendieckTopology (Discrete PUnit.{1})) (Spec (.of k)).smallEtaleTopology := by
  let T : (Spec (.of k)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of k)))
  have : IsIso T.hom := inferInstanceAs (IsIso (𝟙 (Spec (.of k))))
  have hT : IsTerminal T := isTerminalOfIsIsoHom T
  have : (Functor.fromPUnit.{0} T).Full :=
    ⟨fun {X Y} f ↦ ⟨eqToHom (Subsingleton.elim X Y), hT.hom_ext _ _⟩⟩
  have : (Functor.fromPUnit.{0} T).Faithful :=
    ⟨fun {_ _} _ _ _ ↦ Subsingleton.elim _ _⟩
  have : (Functor.fromPUnit.{0} T).IsCoverDense (Spec (.of k)).smallEtaleTopology :=
    ⟨coverByImage_mem_smallEtaleTopology_of_isSepClosed k⟩
  refine { functorPushforward_mem_iff := fun {X S} ↦ ?_ }
  rw [GrothendieckTopology.bot_covering]
  constructor
  · intro hS
    by_contra hne
    have hbot : S = ⊥ := by
      ext Y f
      simp only [Sieve.bot_apply, iff_false]
      intro hf
      obtain rfl : Y = X := Subsingleton.elim _ _
      obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
      exact hne (Sieve.id_mem_iff_eq_top.mp hf)
    subst hbot
    rw [Sieve.functorPushforward_bot, mem_smallEtaleTopology_iff] at hS
    obtain ⟨_, _, h, _⟩ := hS (show Spec (.of k) from default)
    exact h
  · rintro rfl
    rw [Sieve.functorPushforward_top]
    exact GrothendieckTopology.top_mem _ _

/-- **Sheaves on the small étale site of the spectrum of a separably closed field are objects of
the coefficient category**: evaluation at the final object `Spec k` is an equivalence. -/
@[sga "4 VIII 2.4" "more general"]
public theorem isEquivalence_sheafSections_final_of_isSepClosed
    (A : Type*) [Category* A] [HasLimitsOfSize.{0, u} A] :
    ((sheafSections (Spec (.of k)).smallEtaleTopology A).obj
      (op (Scheme.Etale.mk (𝟙 (Spec (.of k)))))).IsEquivalence := by
  let G := Functor.fromPUnit.{0} (Scheme.Etale.mk (𝟙 (Spec (.of k))))
  let E : ((Discrete PUnit.{1})ᵒᵖ ⥤ A) ≌ A :=
    (Discrete.opposite PUnit.{1}).congrLeft.trans Functor.equiv
  let e : G.sheafPushforwardContinuous A ⊥ (Spec (.of k)).smallEtaleTopology ⋙
      (sheafBotEquivalence A).functor ⋙ E.functor ≅
      (sheafSections (Spec (.of k)).smallEtaleTopology A).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of k))))) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm)
  exact Functor.isEquivalence_of_iso e

/-- **Global sections over a separably closed field is an equivalence** from sheaves on the
small étale site of `Spec k` to the coefficient category. -/
public theorem isEquivalence_globalSections_of_isSepClosed
    (A : Type*) [Category* A] [HasLimitsOfSize.{0, u} A]
    [HasWeakSheafify (Spec (.of k)).smallEtaleTopology A] :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology A).IsEquivalence := by
  have := isEquivalence_sheafSections_final_of_isSepClosed k A
  have : IsIso (Scheme.Etale.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (IsIso (𝟙 (Spec (.of k))))
  exact Functor.isEquivalence_of_iso
    (Sheaf.ΓNatIsoSheafSections _ A
      (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 (Spec (.of k)))))).symm

variable (K : Type u) [Field K] [IsSepClosed K] [Algebra k K]

/-- **For an extension `K/k` of separably closed fields, direct image along `Spec K ⟶ Spec k` is
an equivalence**, with coefficients in any category with limits: composed with sections over the
final object of `Spec k` it is sections over the final object of `Spec K`, and both are
equivalences. -/
public theorem isEquivalence_sheafPushforwardContinuous_smallEtaleBaseChange_of_isSepClosed
    (A : Type*) [Category* A] [HasLimitsOfSize.{0, u} A] :
    ((smallEtaleBaseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).sheafPushforwardContinuous
      A (Spec (.of k)).smallEtaleTopology (Spec (.of K)).smallEtaleTopology).IsEquivalence := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Tk : (Spec (.of k)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of k)))
  let TK : (Spec (.of K)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of K)))
  have : IsIso Tk.hom := inferInstanceAs (IsIso (𝟙 (Spec (.of k))))
  have : IsIso TK.hom := inferInstanceAs (IsIso (𝟙 (Spec (.of K))))
  have hT : IsTerminal ((smallEtaleBaseChange g).obj Tk) :=
    isTerminalSmallEtaleBaseChangeObj g (isTerminalOfIsIsoHom Tk)
  let e : (smallEtaleBaseChange g).sheafPushforwardContinuous A (Spec (.of k)).smallEtaleTopology
      (Spec (.of K)).smallEtaleTopology ⋙
      (sheafSections (Spec (.of k)).smallEtaleTopology A).obj (op Tk) ≅
      (sheafSections (Spec (.of K)).smallEtaleTopology A).obj (op TK) :=
    (sheafSections (Spec (.of K)).smallEtaleTopology A).mapIso
      ((isTerminalOfIsIsoHom TK).uniqueUpToIso hT).op
  have := isEquivalence_sheafSections_final_of_isSepClosed k A
  have := isEquivalence_sheafSections_final_of_isSepClosed K A
  have : ((smallEtaleBaseChange g).sheafPushforwardContinuous A (Spec (.of k)).smallEtaleTopology
      (Spec (.of K)).smallEtaleTopology ⋙
      (sheafSections (Spec (.of k)).smallEtaleTopology A).obj (op Tk)).IsEquivalence :=
    Functor.isEquivalence_of_iso e.symm
  exact Functor.isEquivalence_of_comp_right _
    ((sheafSections (Spec (.of k)).smallEtaleTopology A).obj (op Tk))

/-- For an extension `K/k` of separably closed fields, direct image of abelian sheaves along
`Spec K ⟶ Spec k` is an equivalence: the case of abelian coefficients of
`isEquivalence_sheafPushforwardContinuous_smallEtaleBaseChange_of_isSepClosed`. -/
public theorem isEquivalence_etaleAbelianDirectImage_of_isSepClosed :
    (etaleAbelianDirectImage.{u, v}
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsEquivalence :=
  isEquivalence_sheafPushforwardContinuous_smallEtaleBaseChange_of_isSepClosed k K
    AddCommGrpCat.{max (u + 1) v}

/-- **For an extension `K/k` of separably closed fields, inverse image of abelian sheaves along
`Spec K ⟶ Spec k` is an equivalence**, being left adjoint to the direct image, which is one. -/
public theorem isEquivalence_etaleAbelianInverseImage_of_isSepClosed :
    (etaleAbelianInverseImage.{u, v}
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsEquivalence := by
  have := isEquivalence_etaleAbelianDirectImage_of_isSepClosed.{u, v} k K
  exact (etaleAbelianInverseImageDirectImageAdj.{u, v}
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isEquivalence_left_of_isEquivalence_right

end SeparablyClosedField

end Stacks.EtaleCohomology

end
