module


public import StacksFrontier.RingTheory.Etale.FilteredColimit.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.WithTerminal.Lemmas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Colimits of directed systems of filtered colimits of étale algebras

All rings are commutative with unit. An `R`-algebra is a commutative ring `A` equipped
with a ring homomorphism `R → A`, its structure map; morphisms of `R`-algebras are ring
homomorphisms commuting with the structure maps. Colimits are taken in the category of
`R`-algebras; over a directed index they are the usual direct limits.

## Étale algebras

For a ring `R` and an `R`-algebra `A`, the statement that `A` is étale over `R` is the
predicate `Algebra.Etale R A`: smooth of relative dimension `0`, equivalently of finite
presentation, flat and unramified over `R`. This predicate is taken as given.

## Filtered colimits of étale algebras

`A` is a *filtered colimit of étale `R`-algebras* when there are a small filtered category
`J` and a diagram `F : J ⥤ CommAlgCat R` with every `F.obj j` étale over `R`, together
with a colimit cocone for `F` whose apex is isomorphic to `A` as an `R`-algebra: the legs
`F.obj j ⟶ A` commute with the transition maps and satisfy the universal property of the
colimit. This is the genuine categorical colimit of a diagram of étale algebras, and it is
not the same condition as `A` being a directed union of étale `R`-subalgebras of `A`.

The category of `R`-algebras is modelled by `CommAlgCat R`, whose objects are commutative
rings carrying an `R`-algebra structure and whose morphisms are `R`-algebra homomorphisms.
An `R`-algebra isomorphism is precisely an isomorphism in `CommAlgCat R`, so "`A` is a
colimit of `F`" is encoded as a colimit cocone for `F` whose apex is isomorphic, in
`CommAlgCat R`, to `CommAlgCat.of R A`.

## Main result

Let `I` be a directed set and let `i ↦ (R_i → A_i)` be a system of arrows of rings over
`I`: functors `i ↦ R_i` and `i ↦ A_i` from `I` to commutative rings, together with a
natural transformation giving the structure maps `R_i → A_i`, whose naturality squares are
the required commutative squares with the transition maps. Set `R = colim_i R_i` and
`A = colim_i A_i`, and let `R → A` be the induced colimit map, making `A` an `R`-algebra.
If every `A_i` is a filtered colimit of étale `R_i`-algebras, then `A` is a filtered
colimit of étale `R`-algebras.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- `IsFilteredColimitOfEtaleHom` is transported along a ring isomorphism of the target
that is compatible with the structure maps. If `f₁ : R →+* A₁` exhibits `A₁` as a
filtered colimit of étale `R`-algebras and `e : A₁ ≃+* A₂` satisfies
`e ∘ f₁ = f₂`, then `f₂ : R →+* A₂` does too — the apex iso of the colimit cocone
absorbs `e` (as an `R`-algebra iso). -/
lemma IsFilteredColimitOfEtaleHom.transport {R : Type u} [CommRing R]
    {A₁ : Type u} [CommRing A₁] {A₂ : Type u} [CommRing A₂]
    {f₁ : R →+* A₁} {f₂ : R →+* A₂} (h : IsFilteredColimitOfEtaleHom f₁)
    (e : A₁ ≃+* A₂) (he : ∀ r, e (f₁ r) = f₂ r) :
    IsFilteredColimitOfEtaleHom f₂ := by
  let : Algebra R A₁ := f₁.toAlgebra
  let : Algebra R A₂ := f₂.toAlgebra
  obtain ⟨J, instJ, filtJ, F, hEt, c, ⟨eA⟩, ⟨hc⟩⟩ := h
  refine ⟨J, instJ, filtJ, F, hEt, c, ⟨eA ≪≫ CommAlgCat.isoMk
    (@AlgEquiv.ofRingEquiv R A₁ A₂ _ _ _ f₁.toAlgebra f₂.toAlgebra e
      he)⟩, ⟨hc⟩⟩

-- Auxiliary lemmas (the reusable Stacks pieces 0BSH, 0BSJ + the outer-colimit step).

/-! ### Base-change functor for `L_baseChange` (Stacks 0BSH)

The base-change functor `(- ⊗[R] S) : CommAlgCat R ⥤ CommAlgCat S` is realized as
the composite of the equivalence `CommAlgCat R ≌ Under R`, the pushout functor
`Under.pushout g : Under R ⥤ Under S` (a left adjoint, hence colimit-preserving),
and the equivalence `Under S ≌ CommAlgCat S`. On objects it sends `X` to the
pushout of `R → X` and `g : R → S`, which is canonically `S ⊗[R] X`. -/
namespace BaseChangeAux

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] (g : R →+* S)

/-- The base-change functor `(- ⊗[R] S) : CommAlgCat R ⥤ CommAlgCat S`, built from
the `Under`-equivalences and the pushout functor along `g`. -/
@[ega "I 3.3.7" "special case"]
noncomputable def BC : CommAlgCat.{u} R ⥤ CommAlgCat.{u} S :=
  (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
    Under.pushout (CommRingCat.ofHom g) ⋙
    (commAlgCatEquivUnder (CommRingCat.of S)).inverse

/-- `BC g` is a left adjoint (composite of two equivalences and the pushout
functor `Under.pushout g`, which is a left adjoint). -/
noncomputable instance : (BC g).IsLeftAdjoint := by
  unfold BC; infer_instance

variable [Algebra R S]

/-- The carrier-level isomorphism (in `CommRingCat`) between the pushout of
`R → X` and `R → S`, and `S ⊗[R] X`: the pushout is `X ⊗[R] S` (apex of the
explicit pushout cocone), composed with `Algebra.TensorProduct.comm`. -/
noncomputable def rIso (X : CommAlgCat.{u} R) :
    (pushout (CommRingCat.ofHom (algebraMap R (X:Type u))) (CommRingCat.ofHom (algebraMap R S)))
      ≅ CommRingCat.of (TensorProduct R S (X:Type u)) :=
  (CommRingCat.isPushout_tensorProduct R (X:Type u) S).isoPushout.symm ≪≫
    (Algebra.TensorProduct.comm R (X:Type u) S).toRingEquiv.toCommRingCatIso

/-- The `Under S`-isomorphism between `(Under.pushout g).obj (R.mkUnder X)` and
`S.mkUnder (S ⊗[R] X)`: the `rIso` carrier iso intertwines the `S`-structure maps
(`pushout.inr` ↔ `includeLeftRingHom`). -/
noncomputable def underIso (hg : g = algebraMap R S) (X : CommAlgCat.{u} R) :
    (Under.pushout (CommRingCat.ofHom g)).obj
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor.obj X)
    ≅ (CommRingCat.of S).mkUnder (TensorProduct R S (X:Type u)) := by
  subst hg
  refine Under.isoMk (rIso (S := S) X) ?_
  change pushout.inr _ _ ≫ (rIso (S := S) X).hom = _
  simp only [CommRingCat.mkUnder_hom, rIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [CommRingCat.isPushout_tensorProduct R (X:Type u) S |>.inr_isoPushout_inv]
  apply CommRingCat.hom_ext
  ext s
  simp [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.algebraMap_apply]

/-- The object isomorphism `(BC g).obj X ≅ CommAlgCat.of S (S ⊗[R] X)` in
`CommAlgCat S`. -/
noncomputable def objIso (hg : g = algebraMap R S) (X : CommAlgCat.{u} R) :
    (BC g).obj X ≅ CommAlgCat.of S (TensorProduct R S (X:Type u)) :=
  (commAlgCatEquivUnder (CommRingCat.of S)).inverse.mapIso (underIso g hg X) ≪≫
    CommAlgCat.isoMk
      (@AlgEquiv.ofRingEquiv S (TensorProduct R S (X:Type u)) (TensorProduct R S (X:Type u))
        _ _ _
        (CommRingCat.instAlgebraCarrierRight
          ((CommRingCat.of S).mkUnder (TensorProduct R S (X:Type u))))
        Algebra.TensorProduct.leftAlgebra
        (RingEquiv.refl _) (fun _ => rfl))

end BaseChangeAux

/-- **Sub-lemma L_baseChange (Stacks 10.154.1 / 0BSH).**

Base change of a filtered colimit of étale algebras is again a filtered colimit of
étale algebras. Concretely: if `A`, viewed as an `R`-algebra via `f : R →+* A`, is a
filtered colimit of étale `R`-algebras, and `g : R →+* S` is any ring map, then
`S ⊗[R] A`, viewed as an `S`-algebra via the canonical map `S → S ⊗[R] A`, is a
filtered colimit of étale `S`-algebras.

INFORMAL ARGUMENT.
Let `F : J ⥤ CommAlgCat R` be the étale diagram with colimit cocone `c`, apex
`≅ A` over `R`. Base change `(- ⊗[R] S) : CommAlgCat R ⥤ CommAlgCat S` is a left
adjoint (it is left adjoint to restriction of scalars along `g`), hence preserves
all colimits. Therefore:
  (i) the diagram `F ⋙ (- ⊗[R] S) : J ⥤ CommAlgCat S` has every object
      `(F.obj j) ⊗[R] S` étale over `S` — this is exactly `Algebra.Etale.baseChange`
      (Stacks 0BSH); and
  (ii) the image cocone `(- ⊗[R] S).mapCocone c` is again a colimit cocone (left
      adjoints preserve colimits), with apex `(c.pt) ⊗[R] S ≅ A ⊗[R] S` over `S`,
      and `A ⊗[R] S ≅ S ⊗[R] A` as `S`-algebras.
The same filtered index `J` works. Hence `S ⊗[R] A` is a filtered colimit of étale
`S`-algebras with index category `J`.

Mathlib inputs: `Algebra.Etale.baseChange` (étale stable under base change);
the base-change/extension-of-scalars functor on `CommAlgCat` as a left adjoint
(`CategoryTheory.Adjunction`, `Adjunction.isLeftAdjoint`,
`CategoryTheory.Limits.PreservesColimit`); `Algebra.TensorProduct.comm` for the
`S ⊗[R] A ≅ A ⊗[R] S` swap. -/
lemma L_baseChange {R : Type u} [CommRing R] {A : Type u} [CommRing A]
    (f : R →+* A) (hA : IsFilteredColimitOfEtaleHom f)
    {S : Type u} [CommRing S] (g : R →+* S) :
    letI : Algebra R S := g.toAlgebra
    letI : Algebra R A := f.toAlgebra
    IsFilteredColimitOfEtaleHom
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := A)) := by
  let : Algebra R S := g.toAlgebra
  let : Algebra R A := f.toAlgebra
  obtain ⟨J, instJ, filtJ, F, hEt, c, ⟨eA⟩, ⟨hc⟩⟩ := hA
  have hg : g = algebraMap R S := rfl
  refine ⟨J, instJ, filtJ, F ⋙ BaseChangeAux.BC g, ?_, (BaseChangeAux.BC g).mapCocone c,
    ⟨?_⟩, ⟨?_⟩⟩
  · -- Each object `(BC g).obj (F.obj j)` is étale over `S`.
    intro j
    have : Algebra.Etale R (F.obj j) := hEt j
    have : Algebra.Etale S (TensorProduct R S (F.obj j : Type u)) :=
      Algebra.Etale.baseChange R (F.obj j : Type u) S
    exact Algebra.Etale.of_equiv
      (CommAlgCat.isoEquivAlgEquiv (BaseChangeAux.objIso g hg (F.obj j)).symm)
  · -- Apex isomorphism `(BC g).obj c.pt ≅ of S (S ⊗[R] A)`.
    refine (BaseChangeAux.objIso g hg c.pt) ≪≫ ?_
    -- of S (S ⊗[R] c.pt) ≅ of S (S ⊗[R] A) via eA, then bridge to includeLeftRingHom-algebra.
    refine CommAlgCat.isoMk
      (Algebra.TensorProduct.congr (AlgEquiv.refl)
        (CommAlgCat.isoEquivAlgEquiv eA)) ≪≫ ?_
    exact CommAlgCat.isoMk
      (@AlgEquiv.ofRingEquiv S (TensorProduct R S A) (TensorProduct R S A) _ _ _
        Algebra.TensorProduct.leftAlgebra
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := A)).toAlgebra
        (RingEquiv.refl _) (fun _ => rfl))
  · -- The image cocone is a colimit (left adjoints preserve colimits).
    exact isColimitOfPreserves (BaseChangeAux.BC g) hc

/-! ### Slice-category construction for `L_compose` (Stacks 0BSJ)

The proof of `L_compose` follows the *slice-category route*, which avoids the
strictification obstruction of the naïve Grothendieck `I ⥤ Cat` construction.

Given the (extracted) data of the compose situation — a filtered `I`, for each `i`
a filtered `J i` with an étale diagram `F i : J i ⥤ CommAlgCat R` whose colimit is
`G.obj i`, and a colimit `A = colim_I G` — we index the desired étale diagram by the
category `K = KObj D` whose objects are pairs `(i, j)` carrying the *composite*
structure map `φ_{i,j} : (F i).obj j ⟶ A`, and whose morphisms are algebra maps
commuting with the `φ`'s (i.e. `K` is a full subcategory of the slice `CommAlgCat R / A`).
Transition maps in the diagram `H = Kdiagram D` are then *literally* these algebra
maps, so functoriality is on the nose. -/
namespace LComposeAux

universe v

variable {R : Type u} [CommRing R]

/-- **Filtered factorization principle (the analytic kernel of L_compose).**

In a filtered colimit `T = colim_J F` of commutative `R`-algebras with colimit
cocone `cc` (legs `cc.ι.app j : F.obj j ⟶ T`), every map out of a *finitely
presented* `R`-algebra `E` factors (existence), uniquely up to refinement
(uniqueness), through some stage `F.obj j`.

This is the standalone obligation underlying both `Kfiltered` and `Kcolimit`. It
follows from: the forgetful functor `CommAlgCat R ⥤ Type` preserves filtered
colimits (so `T` is, on underlying sets, the set-level filtered colimit), the
explicit `Types`-level description of filtered colimits, and the finite
presentation of `E` (finitely many generators lift to a common stage, finitely
many relations are imposed after a further transition). Every étale `R`-algebra is
finitely presented (`Algebra.Etale.finitePresentation`), so it applies to all the
`(F i).obj j`. -/
@[ega "IV 8.8.2.3" "more general"]
lemma filtered_factorization
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (Fdiag : J ⥤ CommAlgCat.{u} R) (cc : Cocone Fdiag) (hcc : IsColimit cc)
    (E : CommAlgCat.{u} R) (hE : Algebra.FinitePresentation R E) :
    -- existence of a factorization through a stage
    (∀ (a : E ⟶ cc.pt), ∃ (j : J) (ã : E ⟶ Fdiag.obj j), ã ≫ cc.ι.app j = a) ∧
    -- equalization at a finite stage
    (∀ (j : J) (g₁ g₂ : E ⟶ Fdiag.obj j),
        g₁ ≫ cc.ι.app j = g₂ ≫ cc.ι.app j →
        ∃ (j' : J) (m : j ⟶ j'), g₁ ≫ Fdiag.map m = g₂ ≫ Fdiag.map m) := by
  -- `E` finitely presented ⟹ `E` is a finitely presentable object of `CommAlgCat R`
  -- (transport across `commAlgCatEquivUnder` to `Under R`, where finite presentation
  -- of the structure map gives finite presentability). Then apply the general
  -- finitely-presentable-object factorization lemmas to the filtered colimit `cc`.
  have : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  have hfp : CategoryTheory.IsFinitelyPresentable.{u} E := by
    refine (CategoryTheory.isCardinalPresentable_iff_of_isEquivalence E Cardinal.aleph0
      (commAlgCatEquivUnder (CommRingCat.of R)).functor).mp ?_
    apply CommRingCat.isFinitelyPresentable_under
    show (CommRingCat.Hom.hom
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor.obj E).hom).FinitePresentation
    show (algebraMap R (E : Type u)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    exact hE
  refine ⟨?_, ?_⟩
  · -- Existence: a finitely presentable object factors through some stage.
    exact fun a ↦ CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit hcc a
  · -- Equalization: two stage-maps equalized in the colimit are equalized after a
    -- refinement; coequalize the two transition maps from the general lemma.
    intro j g₁ g₂ h
    obtain ⟨k, u, v, huv⟩ :=
      CategoryTheory.IsFinitelyPresentable.exists_eq_of_isColimit hcc g₁ g₂ h
    let w := IsFiltered.coeqHom u v
    have hw : u ≫ w = v ≫ w := IsFiltered.coeq_condition u v
    refine ⟨IsFiltered.coeq u v, u ≫ w, ?_⟩
    have heq : g₁ ≫ Fdiag.map (u ≫ w) = g₂ ≫ Fdiag.map (v ≫ w) := by
      rw [Fdiag.map_comp, Fdiag.map_comp, ← Category.assoc, ← Category.assoc, huv]
    rw [heq, ← hw]

/-- **Étale objects.** Every object of `H` is étale over `R`, provided the inner
diagrams `F i` are étale. -/
lemma Kdiagram_etale (D : KData R)
    (hEt : ∀ (i : D.I) (j : D.J i), Algebra.Etale R ((D.F i).obj j)) :
    ∀ k : KObj D, Algebra.Etale R ((Kdiagram D).obj k) :=
  fun k => hEt k.fst k.snd

/-- Unfolding of the structure map `Kphi` of a `K`-object in terms of the `KSetup`
data: it is the composite leg `ccocone` ≫ `eC` ≫ `dcocone` ≫ `eqToHom`. -/
lemma Kphi_factor (D : KData R) (S : KSetup D) (k : KObj D) :
    Kphi k = (S.ccocone k.fst).ι.app k.snd ≫ (S.eC k.fst).hom
      ≫ S.dcocone.ι.app k.fst ≫ eqToHom S.hTd :=
  S.hφ k.fst k.snd

/-- An algebra map `u` out of `Kalg k` into a stage `(D.F i).obj j` whose composite with the leg
is the transported leg of `k` along `g : k.fst ⟶ i` underlies a `K`-morphism: it is compatible
with the structure maps. -/
private lemma comp_Kphi_of_comp_leg (D : KData R) (S : KSetup D) {k : KObj D} {i : D.I}
    (g : k.fst ⟶ i) (a : (D.F k.fst).obj k.snd ⟶ (S.ccocone i).pt)
    (ha : a = (S.ccocone k.fst).ι.app k.snd ≫ (S.eC k.fst).hom ≫ S.G.map g ≫ (S.eC i).inv)
    {j : D.J i} (u : Kalg k ⟶ (D.F i).obj j) (h : u ≫ (S.ccocone i).ι.app j = a) :
    u ≫ Kphi (⟨i, j⟩ : KObj D) = Kphi k := by
  have e : a ≫ (S.eC i).hom ≫ S.dcocone.ι.app i ≫ eqToHom S.hTd
      = (S.ccocone k.fst).ι.app k.snd ≫ (S.eC k.fst).hom
        ≫ S.dcocone.ι.app k.fst ≫ eqToHom S.hTd := by
    rw [ha]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (S.G.map g), S.dcocone.w g]
  rw [Kphi_factor D S ⟨i, j⟩, Kphi_factor D S k, ← Category.assoc u, h]
  exact e

/-- `filtered_factorization` specialized to the inner colimit `ccocone i`: any map
from an étale `(F i₁).obj j₁` into `(ccocone i).pt` factors through some stage. -/
lemma Kfilt_factor_inner (D : KData R) (S : KSetup D) (i : D.I)
    (E : KObj D) (a : Kalg E ⟶ (S.ccocone i).pt) :
    ∃ (j : D.J i) (ã : Kalg E ⟶ (D.F i).obj j), ã ≫ (S.ccocone i).ι.app j = a := by
  have := S.filtJ i
  have hfp : Algebra.FinitePresentation R (Kalg E) := (S.hEt E.fst E.snd).finitePresentation
  exact (filtered_factorization (D.F i) (S.ccocone i) (S.hc i) (Kalg E) hfp).left a

-- needed: without it `Kfiltered_cocone_objs` fails (4 sites): invalid 'calc' step, failed to
-- synthesize `Trans` instance
set_option backward.isDefEq.respectTransparency false in
/-- The "joint upper bound" obligation for `IsFilteredOrEmpty (KObj D)`. -/
lemma Kfiltered_cocone_objs (D : KData R) (S : KSetup D) (k₁ k₂ : KObj D) :
    ∃ (k : KObj D) (_ : k₁ ⟶ k) (_ : k₂ ⟶ k), True := by
  have := S.filtI
  -- common outer index
  set i := IsFiltered.max k₁.fst k₂.fst with hi
  set g₁ := IsFiltered.leftToMax k₁.fst k₂.fst with hg₁
  set g₂ := IsFiltered.rightToMax k₁.fst k₂.fst with hg₂
  -- maps into `(ccocone i).pt`
  set a₁ : Kalg k₁ ⟶ (S.ccocone i).pt :=
    (S.ccocone k₁.fst).ι.app k₁.snd ≫ (S.eC k₁.fst).hom ≫ S.G.map g₁ ≫ (S.eC i).inv with ha₁
  set a₂ : Kalg k₂ ⟶ (S.ccocone i).pt :=
    (S.ccocone k₂.fst).ι.app k₂.snd ≫ (S.eC k₂.fst).hom ≫ S.G.map g₂ ≫ (S.eC i).inv with ha₂
  obtain ⟨j₁', ã₁, hã₁⟩ := Kfilt_factor_inner D S i k₁ a₁
  obtain ⟨j₂', ã₂, hã₂⟩ := Kfilt_factor_inner D S i k₂ a₂
  have := S.filtJ i
  set jm := IsFiltered.max j₁' j₂' with hjm
  set m₁ := IsFiltered.leftToMax j₁' j₂' with hm₁
  set m₂ := IsFiltered.rightToMax j₁' j₂' with hm₂
  refine ⟨⟨i, jm⟩, ?_, ?_, trivial⟩
  · -- morphism k₁ ⟶ ⟨i, jm⟩
    refine { u := ã₁ ≫ (D.F i).map m₁,
             w := comp_Kphi_of_comp_leg D S g₁ a₁ ha₁ _ ?_ }
    rw [Category.assoc, (S.ccocone i).w m₁]
    exact hã₁
  · -- morphism k₂ ⟶ ⟨i, jm⟩
    refine { u := ã₂ ≫ (D.F i).map m₂,
             w := comp_Kphi_of_comp_leg D S g₂ a₂ ha₂ _ ?_ }
    rw [Category.assoc, (S.ccocone i).w m₂]
    exact hã₂

/-- Two `K`-morphisms with equal underlying algebra maps are equal (the slice
condition `w` is a proposition). -/
lemma KHom_eq_of_u {D : KData R} {k k' : KObj D} (a b : k ⟶ k')
    (h : (a : KHom k k').u = (b : KHom k k').u) : a = b := by
  obtain ⟨au, aw⟩ := a
  obtain ⟨bu, bw⟩ := b
  cases h
  rfl

/-- `filtered_factorization` equalization clause specialized to the inner colimit
`ccocone i`: two maps into a stage equalized by the leg are equalized after a
transition. -/
lemma Kfilt_eq_inner (D : KData R) (S : KSetup D) (i : D.I)
    (E : KObj D) (j : D.J i) (g₁ g₂ : Kalg E ⟶ (D.F i).obj j)
    (h : g₁ ≫ (S.ccocone i).ι.app j = g₂ ≫ (S.ccocone i).ι.app j) :
    ∃ (j' : D.J i) (m : j ⟶ j'), g₁ ≫ (D.F i).map m = g₂ ≫ (D.F i).map m := by
  have := S.filtJ i
  have hfp : Algebra.FinitePresentation R (Kalg E) := (S.hEt E.fst E.snd).finitePresentation
  exact (filtered_factorization (D.F i) (S.ccocone i) (S.hc i) (Kalg E) hfp).right j g₁ g₂ h

-- needed: without it `Kfiltered_cocone_maps` fails (5 sites): Tactic `rewrite` failed: Did not
-- find an occurrence of the pat…
set_option backward.isDefEq.respectTransparency false in
/-- The "coequalize a parallel pair" obligation for `IsFilteredOrEmpty (KObj D)`. -/
lemma Kfiltered_cocone_maps (D : KData R) (S : KSetup D) (k₁ k₂ : KObj D)
    (u v : k₁ ⟶ k₂) :
    ∃ (k₃ : KObj D) (h : k₂ ⟶ k₃), u ≫ h = v ≫ h := by
  have := S.filtI
  -- (**) the two underlying maps agree after `Kphi k₂`.
  have hstar : (u.u ≫ (S.ccocone k₂.fst).ι.app k₂.snd ≫ (S.eC k₂.fst).hom)
        ≫ S.dcocone.ι.app k₂.fst
      = (v.u ≫ (S.ccocone k₂.fst).ι.app k₂.snd ≫ (S.eC k₂.fst).hom)
        ≫ S.dcocone.ι.app k₂.fst := by
    have huw := u.w
    have hvw := v.w
    rw [Kphi_factor D S k₂] at huw hvw
    -- huw, hvw : *.u ≫ (cc ≫ eC ≫ d ≫ eqToHom) = Kphi k₁
    have key : u.u ≫ (S.ccocone k₂.fst).ι.app k₂.snd ≫ (S.eC k₂.fst).hom
          ≫ S.dcocone.ι.app k₂.fst ≫ eqToHom S.hTd
        = v.u ≫ (S.ccocone k₂.fst).ι.app k₂.snd ≫ (S.eC k₂.fst).hom
          ≫ S.dcocone.ι.app k₂.fst ≫ eqToHom S.hTd := by
      rw [huw, hvw]
    -- cancel the trailing iso `eqToHom`
    have := congrArg (· ≫ eqToHom S.hTd.symm) key
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using this
  -- Outer equalization: get `g : k₂.fst ⟶ i₃` with `(†)`.
  have hfp₁ : Algebra.FinitePresentation R (Kalg k₁) := (S.hEt k₁.fst k₁.snd).finitePresentation
  obtain ⟨i₃, g, hg⟩ :=
    (filtered_factorization S.G S.dcocone S.hd (Kalg k₁) hfp₁).right k₂.fst
      (u.u ≫ (S.ccocone k₂.fst).ι.app k₂.snd ≫ (S.eC k₂.fst).hom)
      (v.u ≫ (S.ccocone k₂.fst).ι.app k₂.snd ≫ (S.eC k₂.fst).hom)
      hstar
  -- hg : (u.u ≫ cc ≫ eC) ≫ G.map g = (v.u ≫ cc ≫ eC) ≫ G.map g
  -- Factor `b` through a stage of `ccocone i₃`.
  set b : Kalg k₂ ⟶ (S.ccocone i₃).pt :=
    (S.ccocone k₂.fst).ι.app k₂.snd ≫ (S.eC k₂.fst).hom ≫ S.G.map g ≫ (S.eC i₃).inv with hb
  obtain ⟨j₃, bt, hbt⟩ := Kfilt_factor_inner D S i₃ k₂ b
  -- The morphism `w : k₂ ⟶ ⟨i₃, j₃⟩`.
  -- `u.u ≫ bt` and `v.u ≫ bt` become equal after the leg `ccocone i₃`.
  have heqleg : (u.u ≫ bt) ≫ (S.ccocone i₃).ι.app j₃
      = (v.u ≫ bt) ≫ (S.ccocone i₃).ι.app j₃ := by
    have hbb : bt ≫ (S.ccocone i₃).ι.app j₃ = b := hbt
    rw [Category.assoc, Category.assoc, hbb, hb]
    -- goal: u.u ≫ (cc ≫ eC ≫ G g ≫ inv) = v.u ≫ (cc ≫ eC ≫ G g ≫ inv)
    simpa only [Category.assoc] using congrArg (· ≫ (S.eC i₃).inv) hg
  -- Inner equalization at `j₃`.
  obtain ⟨j₄, m, hm⟩ := Kfilt_eq_inner D S i₃ k₁ j₃ (u.u ≫ bt) (v.u ≫ bt) heqleg
  -- Build the coequalizing morphism `h : k₂ ⟶ ⟨i₃, j₄⟩`.
  refine ⟨⟨i₃, j₄⟩, { u := bt ≫ (D.F i₃).map m, w := ?_ }, ?_⟩
  · -- structure-map compatibility for `h`.
    refine comp_Kphi_of_comp_leg D S g b hb _ ?_
    rw [Category.assoc, (S.ccocone i₃).w m]
    exact hbt
  · -- `u ≫ h = v ≫ h`.
    apply KHom_eq_of_u
    show u.u ≫ (bt ≫ (D.F i₃).map m) = v.u ≫ (bt ≫ (D.F i₃).map m)
    rw [← Category.assoc, ← Category.assoc]
    exact hm

/-- **`K` is filtered.** Joint upper bounds and coequalization are obtained by
repeatedly applying `filtered_factorization` (sources are étale, hence finitely
presented) to push finitely many pieces of data to common stages, using
filteredness of `I` and the `J i` and the cocone identities. -/
lemma Kfiltered (D : KData R) (S : KSetup D) : IsFiltered (KObj D) := by
  have := S.filtI
  have : IsFilteredOrEmpty (KObj D) :=
    { cocone_objs := fun X Y => by
        obtain ⟨k, f, g, _⟩ := Kfiltered_cocone_objs D S X Y
        exact ⟨k, f, g, trivial⟩
      cocone_maps := fun X Y f g => Kfiltered_cocone_maps D S X Y f g }
  have : Nonempty (KObj D) := by
    obtain ⟨i⟩ := (S.filtI).nonempty
    obtain ⟨j⟩ := (S.filtJ i).nonempty
    exact ⟨⟨i, j⟩⟩
  exact IsFiltered.mk

/-- If an algebra map `ã : Kalg ⟨i,j⟩ ⟶ (D.F i').obj j'` is compatible with the
structure maps to `T` (i.e. `ã ≫ Kphi ⟨i',j'⟩ = Kphi ⟨i,j⟩`), then `ã` is the
underlying map of a `K`-morphism, so it commutes with the colimit legs. -/
lemma Kcolimit_ι_comp {D : KData R} {L : CommAlgCat.{u} R}
    (ιL : ∀ k : KObj D, Kalg k ⟶ L)
    (hιL : ∀ {k k' : KObj D} (f : k ⟶ k'), f.u ≫ ιL k' = ιL k)
    {k k' : KObj D} (ã : Kalg k ⟶ Kalg k')
    (hã : ã ≫ Kphi k' = Kphi k) :
    ã ≫ ιL k' = ιL k :=
  hιL (k := k) (k' := k') { u := ã, w := hã }

-- needed: without it `Kcolimit` fails (8 sites): Tactic `rewrite` failed: Did not find an
-- occurrence of the pat…
set_option backward.isDefEq.respectTransparency false in
-- this proof's elaboration needs more than the default heartbeat budget
/-- **`Φ` is a colimit cocone**, so `T` (`= A`) is the colimit of the étale diagram
`H`. We build the inverse `ψ : T ⟶ colim H` to the comparison map `θ` purely
categorically: nested universal properties of the inner colimits `ccocone i` and
the outer colimit `dcocone`, with the cross-stage compatibility supplied by the
inner factorization principle `Kfilt_factor_inner` exactly as in
`Kfiltered_cocone_objs`. Then `θ` is an isomorphism and `IsColimit.ofPointIso`
finishes. -/
lemma Kcolimit (D : KData R) (S : KSetup D) :
    Nonempty (IsColimit (Kcocone D)) := by
  have : IsFiltered (KObj D) := Kfiltered D S
  -- The chosen colimit cocone `cc` of `Kdiagram D`, its colimit witness and legs.
  let cc : Cocone (Kdiagram D) := colimit.cocone (Kdiagram D)
  let hcL : IsColimit cc := colimit.isColimit (Kdiagram D)
  let L : CommAlgCat.{u} R := cc.pt
  let ιL : ∀ k : KObj D, Kalg k ⟶ L := fun k => cc.ι.app k
  -- Legs respect `K`-morphisms.
  have hιLnat : ∀ {k k' : KObj D} (f : k ⟶ k'), f.u ≫ ιL k' = ιL k := fun f ↦ cc.w f
  -- For each outer index `i`, the cocone on `D.F i` with apex `L`,
  -- legs `ιL ⟨i, j⟩`.
  let χ : ∀ i, Cocone (D.F i) := fun i =>
    { pt := L
      ι := { app := fun j => ιL ⟨i, j⟩
             naturality := by
               intro j j' m
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
               -- `(D.F i).map m` underlies the `K`-morphism `⟨i,j⟩ ⟶ ⟨i,j'⟩`.
               refine hιLnat (k := ⟨i, j⟩) (k' := ⟨i, j'⟩)
                 { u := (D.F i).map m, w := ?_ }
               rw [Kphi_factor D S ⟨i, j'⟩, Kphi_factor D S ⟨i, j⟩,
                 ← Category.assoc, (S.ccocone i).w m] } }
  -- Inner desc: `ψi i : (ccocone i).pt ⟶ L`.
  let ψi : ∀ i, (S.ccocone i).pt ⟶ L := fun i => (S.hc i).desc (χ i)
  have hψi_fac : ∀ i (j : D.J i), (S.ccocone i).ι.app j ≫ ψi i = ιL ⟨i, j⟩ :=
    fun i j ↦ (S.hc i).fac (χ i) j
  -- Outer cocone on `S.G` with apex `L`, legs `μ i = (eC i).inv ≫ ψi i`.
  let μ : ∀ i, S.G.obj i ⟶ L := fun i => (S.eC i).inv ≫ ψi i
  have hμnat : ∀ {i i' : D.I} (g : i ⟶ i'), S.G.map g ≫ μ i' = μ i := by
    intro i i' g
    -- Suffices: `(eC i).hom ≫ G.map g ≫ μ i' = ψi i`, then cancel `(eC i).inv`.
    have key : (S.eC i).hom ≫ S.G.map g ≫ μ i' = ψi i := by
      -- Both maps `(ccocone i).pt ⟶ L`; check after the legs of `ccocone i`.
      refine (S.hc i).hom_ext ?_
      intro j
      -- LHS leg: factor `a` through a stage of `ccocone i'`.
      set a : Kalg (⟨i, j⟩ : KObj D) ⟶ (S.ccocone i').pt :=
        (S.ccocone i).ι.app j ≫ (S.eC i).hom ≫ S.G.map g ≫ (S.eC i').inv with ha
      obtain ⟨j', ã, hã⟩ := Kfilt_factor_inner D S i' ⟨i, j⟩ a
      -- `ã` underlies a `K`-morphism `⟨i,j⟩ ⟶ ⟨i',j'⟩`.
      have hãw : ã ≫ Kphi (⟨i', j'⟩ : KObj D) = Kphi (⟨i, j⟩ : KObj D) :=
        comp_Kphi_of_comp_leg D S (k := ⟨i, j⟩) g a ha ã hã
      -- Now compute both sides at leg `j`.
      show (S.ccocone i).ι.app j ≫ (S.eC i).hom ≫ S.G.map g ≫ (S.eC i').inv ≫ ψi i'
          = (S.ccocone i).ι.app j ≫ ψi i
      calc (S.ccocone i).ι.app j ≫ (S.eC i).hom ≫ S.G.map g ≫ (S.eC i').inv ≫ ψi i'
          = a ≫ ψi i' := by
            rw [ha]; simp only [Category.assoc]
        _ = (ã ≫ (S.ccocone i').ι.app j') ≫ ψi i' := by rw [hã]
        _ = ã ≫ (S.ccocone i').ι.app j' ≫ ψi i' := by simp only [Category.assoc]
        _ = ã ≫ ιL ⟨i', j'⟩ := by rw [hψi_fac i' j']
        _ = ιL ⟨i, j⟩ := hιLnat (k := ⟨i, j⟩) (k' := ⟨i', j'⟩) { u := ã, w := hãw }
        _ = (S.ccocone i).ι.app j ≫ ψi i := (hψi_fac i j).symm
    -- cancel `(eC i).inv`
    show S.G.map g ≫ (S.eC i').inv ≫ ψi i' = (S.eC i).inv ≫ ψi i
    rw [← key]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  let Gcocone : Cocone S.G :=
    { pt := L
      ι := { app := μ
             naturality := by
               intro i i' g
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
               exact hμnat g } }
  -- Outer desc, then the inverse map `ψ : D.T ⟶ L`.
  let ψT : S.dcocone.pt ⟶ L := S.hd.desc Gcocone
  have hψT_fac : ∀ i, S.dcocone.ι.app i ≫ ψT = μ i := fun i => S.hd.fac Gcocone i
  let ψ : D.T ⟶ L := eqToHom S.hTd.symm ≫ ψT
  -- The comparison map `θ : L ⟶ D.T`.
  let θ : L ⟶ D.T := hcL.desc (Kcocone D)
  have hθ_fac : ∀ k : KObj D, ιL k ≫ θ = Kphi k := fun k => hcL.fac (Kcocone D) k
  -- The key relation: `Kphi k ≫ ψ = ιL k`.
  have hkey : ∀ k : KObj D, Kphi k ≫ ψ = ιL k := by
    intro k
    show Kphi k ≫ eqToHom S.hTd.symm ≫ ψT = ιL k
    rw [Kphi_factor D S k]
    calc (S.ccocone k.fst).ι.app k.snd ≫ (S.eC k.fst).hom
            ≫ S.dcocone.ι.app k.fst ≫ eqToHom S.hTd ≫ eqToHom S.hTd.symm ≫ ψT
        = (S.ccocone k.fst).ι.app k.snd ≫ (S.eC k.fst).hom
            ≫ S.dcocone.ι.app k.fst ≫ ψT := by
          rw [← Category.assoc (eqToHom S.hTd), eqToHom_trans, eqToHom_refl, Category.id_comp]
      _ = (S.ccocone k.fst).ι.app k.snd ≫ (S.eC k.fst).hom ≫ μ k.fst := by
          rw [hψT_fac k.fst]
      _ = (S.ccocone k.fst).ι.app k.snd ≫ (S.eC k.fst).hom ≫ (S.eC k.fst).inv ≫ ψi k.fst := by
          rfl
      _ = (S.ccocone k.fst).ι.app k.snd ≫ ψi k.fst := by
          simp only [Iso.hom_inv_id_assoc]
      _ = ιL k := hψi_fac k.fst k.snd
  -- `θ ≫ ψ = 𝟙 L`.
  have hθψ : θ ≫ ψ = 𝟙 L := by
    refine hcL.hom_ext ?_
    intro k
    show ιL k ≫ θ ≫ ψ = ιL k ≫ 𝟙 L
    rw [← Category.assoc, hθ_fac k, hkey k, Category.comp_id]
  -- `ψ ≫ θ = 𝟙 T`.
  have hψθ : ψ ≫ θ = 𝟙 D.T := by
    -- check after `eqToHom S.hTd` (i.e. as maps `dcocone.pt ⟶ T`) and the colimit legs
    have h1 : eqToHom S.hTd ≫ ψ ≫ θ = eqToHom S.hTd ≫ 𝟙 D.T := by
      refine S.hd.hom_ext ?_
      intro i
      show S.dcocone.ι.app i ≫ eqToHom S.hTd ≫ ψ ≫ θ
        = S.dcocone.ι.app i ≫ eqToHom S.hTd ≫ 𝟙 D.T
      -- precompose the iso `eC i` so we can use the inner colimit `ccocone i`
      refine (cancel_epi (S.eC i).hom).mp ?_
      refine (S.hc i).hom_ext ?_
      intro j
      have hphi : Kphi (⟨i, j⟩ : KObj D)
          = (S.ccocone i).ι.app j ≫ (S.eC i).hom ≫ S.dcocone.ι.app i ≫ eqToHom S.hTd :=
        Kphi_factor D S ⟨i, j⟩
      show (S.ccocone i).ι.app j ≫ (S.eC i).hom
          ≫ S.dcocone.ι.app i ≫ eqToHom S.hTd ≫ ψ ≫ θ
        = (S.ccocone i).ι.app j ≫ (S.eC i).hom
          ≫ S.dcocone.ι.app i ≫ eqToHom S.hTd ≫ 𝟙 D.T
      calc (S.ccocone i).ι.app j ≫ (S.eC i).hom
              ≫ S.dcocone.ι.app i ≫ eqToHom S.hTd ≫ ψ ≫ θ
          = Kphi (⟨i, j⟩ : KObj D) ≫ ψ ≫ θ := by
            rw [hphi]; simp only [Category.assoc]
        _ = ιL ⟨i, j⟩ ≫ θ := by rw [← Category.assoc (Kphi _), hkey ⟨i, j⟩]
        _ = Kphi (⟨i, j⟩ : KObj D) := hθ_fac ⟨i, j⟩
        _ = (S.ccocone i).ι.app j ≫ (S.eC i).hom
              ≫ S.dcocone.ι.app i ≫ eqToHom S.hTd := by
            rw [hphi]
        _ = (S.ccocone i).ι.app j ≫ (S.eC i).hom
              ≫ S.dcocone.ι.app i ≫ eqToHom S.hTd ≫ 𝟙 D.T := by
            simp only [Category.comp_id]
    exact (cancel_epi (eqToHom S.hTd)).mp h1
  -- `θ` is an isomorphism, hence `Kcocone D` is a colimit via `ofPointIso`.
  have : IsIso θ := ⟨ψ, hθψ, hψθ⟩
  have : IsIso (hcL.desc (Kcocone D)) := this
  exact ⟨IsColimit.ofPointIso hcL⟩

/-- **Assembly.** From a `KData` with a valid `KSetup`, the apex `D.T` is a filtered
colimit of étale `R`-algebras. (Pure glue: combine `Kfiltered`, `Kdiagram_etale`,
`Kcolimit`; the apex iso is the identity since `Kcocone D` has apex `D.T`.) -/
lemma Kassemble (D : KData R) (S : KSetup D)
    {A : Type u} [CommRing A] (f : R →+* A)
    (hfA : letI : Algebra R A := f.toAlgebra; Nonempty (D.T ≅ CommAlgCat.of R A)) :
    IsFilteredColimitOfEtaleHom f := by
  let : Algebra R A := f.toAlgebra
  have : IsFiltered (KObj D) := Kfiltered D S
  obtain ⟨hcolim⟩ := Kcolimit D S
  obtain ⟨eA⟩ := hfA
  refine ⟨KObj D, inferInstance, inferInstance, Kdiagram D,
    Kdiagram_etale D S.hEt, Kcocone D, ⟨?_, ⟨hcolim⟩⟩⟩
  -- `(Kcocone D).pt = D.T` definitionally, so `eA` provides the apex iso.
  exact ⟨eA⟩

end LComposeAux

/-- **Sub-lemma L_compose (Stacks 10.154.3 / 0BSJ).**

A filtered colimit of `R`-algebras, each of which is itself a filtered colimit of
étale `R`-algebras, is again a filtered colimit of étale `R`-algebras.

We phrase the hypothesis categorically: `G : I ⥤ CommAlgCat R` is a diagram over a
small filtered category `I`, with a colimit cocone `d` whose apex is `≅ A` over `R`,
and every object `G.obj i` is a filtered colimit of étale `R`-algebras (via its
own structure map `algebraMap R (G.obj i)`). Conclusion: `A` (via `f`) is a
filtered colimit of étale `R`-algebras.

INFORMAL ARGUMENT (Grothendieck flattening).
For each `i : I` choose, from `hG i`, a small filtered category `J i`, an étale
diagram `Fᵢ : J i ⥤ CommAlgCat R`, and a colimit cocone with apex `≅ G.obj i`.
Form the Grothendieck construction `K = ∫ (i ↦ J i)` — its objects are pairs
`(i, j)` with `i : I`, `j : J i`. Because `I` is filtered and each `J i` is
filtered (and the reindexing functors `J i → J i'` along `i ≤ i'` are obtained
from the étale presentations via the universal property), `K` is filtered
(Grothendieck construction of a filtered diagram of filtered categories is
filtered). Assemble a single diagram `H : K ⥤ CommAlgCat R` sending `(i,j)` to the
étale algebra `(Fᵢ).obj j`; every object is étale over `R`. The iterated-colimit
isomorphism `colim_{(i,j)} H ≅ colim_i (colim_j Fᵢ) ≅ colim_i (G.obj i) ≅ A`
exhibits `A` as the colimit of the filtered étale diagram `H`. Hence `A` is a
filtered colimit of étale `R`-algebras with index category `K`.

Mathlib inputs: `CategoryTheory.Grothendieck`; filteredness of the Grothendieck
construction of a filtered family of filtered categories
(`CategoryTheory.IsFiltered`); the iterated/colimit-of-colimits comparison
(`CategoryTheory.Limits.colimitColimitIso`-style results, or constructed from the
universal properties of the colimit cocones). This is the main formal burden. -/
lemma L_compose {R : Type u} [CommRing R] {A : Type u} [CommRing A]
    (f : R →+* A)
    (I : Type u) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ CommAlgCat.{u} R)
    (hG : ∀ i, IsFilteredColimitOfEtaleHom (algebraMap R (G.obj i)))
    (d : Cocone G) (hd : IsColimit d)
    (hiso : letI : Algebra R A := f.toAlgebra
            Nonempty (d.pt ≅ CommAlgCat.of R A)) :
    IsFilteredColimitOfEtaleHom f := by
  -- Slice-category route.
  classical
  -- Extract the per-`i` étale presentations from `hG`.
  have hG' := hG
  unfold IsFilteredColimitOfEtaleHom at hG'
  choose J instJ Jfilt F hEt c hc using hG'
  -- Apex isos `(c i).pt ≅ CommAlgCat.of R (G.obj i)` and colimit witnesses.
  have eC' := fun i => (hc i).left.some
  have hcolim : ∀ i, IsColimit (c i) := fun i => (hc i).right.some
  -- Compose the apex iso with the canonical iso to `G.obj i`. The bridge iso
  -- reconciles the `.toAlgebra`-induced algebra instance on the `of`-wrapped
  -- target with the native algebra instance of `G.obj i` (same `algebraMap`).
  have eC : ∀ i, (c i).pt ≅ G.obj i := fun i =>
    (eC' i) ≪≫ CommAlgCat.isoMk
      (@AlgEquiv.ofRingEquiv R (G.obj i) (G.obj i) _ _ _
        (algebraMap R (G.obj i)).toAlgebra (G.obj i).algebra (RingEquiv.refl _) (fun _ => rfl))
  -- Build the bundled data `D`.
  set D : LComposeAux.KData R :=
    { I := I, instI := inferInstance, J := J, instJ := instJ, F := F, T := d.pt,
      φ := fun i j => (c i).ι.app j ≫ (eC i).hom ≫ d.ι.app i } with hD
  -- Assemble the `KSetup`.
  have S : LComposeAux.KSetup D :=
    { filtI := ‹IsFiltered I›, filtJ := Jfilt, G := G, dcocone := d, hd := hd,
      hTd := rfl, ccocone := c, hc := hcolim,
      eC := eC,
      hφ := by
        intro i j
        show (c i).ι.app j ≫ (eC i).hom ≫ d.ι.app i
          = (c i).ι.app j ≫ (eC i).hom ≫ d.ι.app i ≫ eqToHom rfl
        simp only [eqToHom_refl, Category.comp_id],
      hEt := hEt }
  -- Apply the assembly lemma; the apex iso `d.pt ≅ CommAlgCat.of R A` is `hiso`.
  exact LComposeAux.Kassemble D S f hiso

/-! ### Diagram and sub-lemmas for `L_outer` (Stacks 0GIM step 1)

The outer diagram `i ↦ A_i ⊗_{R_i} R` is realized in `Under R` as the pushout of
the span `A_i ⟵α_i⟵ R_i ⟶ι⟶ R` (its `R`-structure being `pushout.inr`), then
transported to `CommAlgCat R` via the equivalence `CommAlgCat R ≌ Under R`. -/

-- needed: without it `Gunder` fails (2 sites): unsolved goals
set_option backward.isDefEq.respectTransparency false in
/-- The outer diagram in `Under R`: `i ↦ pushout (α.app i) (colimit.ι 𝓡 i)`
(the base change `A_i ⊗_{R_i} R`), with `R`-structure `pushout.inr` and transition
maps via `pushout.map` along `(𝓐.map h, 𝟙 R, 𝓡.map h)`. -/
noncomputable def Gunder
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (𝓡 𝓐 : I ⥤ CommRingCat.{u}) (α : 𝓡 ⟶ 𝓐) : I ⥤ Under (colimit 𝓡) where
  obj i := Under.mk (pushout.inr (α.app i) (colimit.ι 𝓡 i))
  map {i i'} (h : i ⟶ i') :=
    Under.homMk
      (pushout.map (α.app i) (colimit.ι 𝓡 i) (α.app i') (colimit.ι 𝓡 i')
        (𝓐.map h) (𝟙 _) (𝓡.map h) (α.naturality h).symm (by simp [colimit.w]))
      (by simp [pushout.map])
  map_id i := by
    apply Under.UnderMorphism.ext
    simp only [Under.homMk_right, Under.id_right]
    refine pushout.hom_ext ?_ ?_ <;>
      simp only [pushout.map, CategoryTheory.Functor.map_id, Category.id_comp,
        pushout.desc_inl_inr] <;>
      exact (Category.comp_id _).symm
  map_comp {i j k} f g := by
    apply Under.UnderMorphism.ext
    simp only [Under.homMk_right, Under.comp_right]
    refine pushout.hom_ext ?_ ?_ <;>
      simp [pushout.map, Functor.map_comp]

/-- The outer diagram in `CommAlgCat R`, obtained from `Gunder` via the equivalence
`CommAlgCat R ≌ Under R`. This is the `G` returned by `L_outer`. -/
noncomputable def Galg
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (𝓡 𝓐 : I ⥤ CommRingCat.{u}) (α : 𝓡 ⟶ 𝓐) :
    I ⥤ CommAlgCat.{u} (colimit 𝓡 : CommRingCat).carrier :=
  Gunder I 𝓡 𝓐 α ⋙ (commAlgCatEquivUnder (CommRingCat.of (colimit 𝓡 : CommRingCat).carrier)).inverse

/-- **L_outer_hG (Stacks 0BSH applied per-object).** Each object `Galg.obj i` of the
outer diagram — the base change `A_i ⊗_{R_i} R` — is a filtered colimit of étale
`R`-algebras. This is `L_baseChange` (already proven) applied to `hetale i` along the
colimit ring map `g = (colimit.ι 𝓡 i).hom : R_i → R`, bridged through
`BaseChangeAux.objIso` to the algebra structure on `Galg.obj i`. -/
lemma L_outer_hG
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (𝓡 𝓐 : I ⥤ CommRingCat.{u}) (α : 𝓡 ⟶ 𝓐)
    (hetale : ∀ i, IsFilteredColimitOfEtaleHom (α.app i).hom) (i : I) :
    IsFilteredColimitOfEtaleHom
      (algebraMap (colimit 𝓡 : CommRingCat).carrier (Galg I 𝓡 𝓐 α |>.obj i)) := by
  -- `Galg.obj i` is the SAME composite `commAlgCatEquivUnder.functor ⋙ Under.pushout ⋙ inverse`
  -- as `BaseChangeAux.BC (colimit.ι 𝓡 i).hom` applied to the R_i-algebra A_i.
  -- Apply L_baseChange to `hetale i` along `g = (colimit.ι 𝓡 i).hom`, then transport the
  -- resulting `IsFilteredColimitOfEtaleHom` across the algebra-structure iso
  -- `BaseChangeAux.objIso` / `Algebra.TensorProduct.includeLeftRingHom` ↔ `algebraMap R (Galg.obj
  -- i)`.
  -- conventions match).
  have hetale_i := hetale i
  let : Algebra (𝓡.obj i : CommRingCat).carrier (𝓐.obj i : CommRingCat).carrier := (α.app
      i).hom.toAlgebra
  let : Algebra (𝓡.obj i : CommRingCat).carrier (colimit 𝓡 : CommRingCat).carrier := (colimit.ι 𝓡
      i).hom.toAlgebra
  have hbc := L_baseChange (α.app i).hom hetale_i (colimit.ι 𝓡 i).hom
  -- The R_i-algebra A_i as a CommAlgCat object.
  set Ai : CommAlgCat.{u} (𝓡.obj i : CommRingCat).carrier :=
    CommAlgCat.of (𝓡.obj i : CommRingCat).carrier (𝓐.obj i : CommRingCat).carrier with hAi
  -- `Galg.obj i` is defeq to `(BC g).obj Ai`.
  have hgalg : (Galg I 𝓡 𝓐 α).obj i
      = (BaseChangeAux.BC (colimit.ι 𝓡 i).hom).obj Ai := by
    rfl
  have hobj := BaseChangeAux.objIso (R := (𝓡.obj i : CommRingCat).carrier)
    (S := (colimit 𝓡 : CommRingCat).carrier) (colimit.ι 𝓡 i).hom rfl Ai
  -- AlgEquiv from objIso.symm : of R (R ⊗ A_i) ≅ (BC g).obj Ai = Galg.obj i
  have ealg := CommAlgCat.isoEquivAlgEquiv hobj.symm
  refine hbc.transport ealg.toRingEquiv ?_
  intro r
  have h1 : Algebra.TensorProduct.includeLeftRingHom r
      = algebraMap (colimit 𝓡 : CommRingCat).carrier
          (TensorProduct (𝓡.obj i : CommRingCat).carrier (colimit 𝓡 : CommRingCat).carrier (Ai :
              Type u)) r := rfl
  rw [h1]
  show ealg (algebraMap _ _ r) = _
  rw [AlgEquiv.commutes]
  rfl

-- needed: without it `L_outer_apex` fails (8 sites): Tactic `rewrite` failed: Did not find an
-- occurrence of the pat…
set_option backward.isDefEq.respectTransparency false in
/-- **L_outer_apex (Stacks 0GIM step 1: colimits commute with tensor).** The colimit
of the outer diagram `Galg` is `A = colimit 𝓐` as an `R`-algebra. Equivalently, at the
`CommRingCat` level, `colimᵢ pushout(α_i, ι_i) ≅ colimit 𝓐`. Built from: the explicit
colimit cocone of `Gunder` transported through `commAlgCatEquivUnder.inverse`
(an equivalence, hence colimit-preserving) and `Under.forget R`, plus the Fubini /
colimit-tensor commutation iso identifying its apex with `colimit 𝓐`. -/
lemma L_outer_apex
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (𝓡 𝓐 : I ⥤ CommRingCat.{u}) (α : 𝓡 ⟶ 𝓐) :
    letI : Algebra (colimit 𝓡 : CommRingCat).carrier (colimit 𝓐 : CommRingCat).carrier :=
      (colimMap α).hom.toAlgebra
    Nonempty (((commAlgCatEquivUnder
        (CommRingCat.of (colimit 𝓡 : CommRingCat).carrier)).inverse.mapCocone
          (colimit.cocone (Gunder I 𝓡 𝓐 α))).pt
      ≅ CommAlgCat.of (colimit 𝓡 : CommRingCat).carrier
          (colimit 𝓐 : CommRingCat).carrier) := by
  -- Reduce to `CommRingCat`: `colimit (Gunder ⋙ Under.forget R) ≅ colimit 𝓐`.
  -- Route (Fubini): span `𝓐 ⟵α⟵ 𝓡 ⟶ιnat⟶ constR` in `I ⥤ CommRingCat`; its pointwise
  -- pushout is `Gunder ⋙ Under.forget R`; `colim` (left adjoint) preserves the pushout,
  -- giving `pushout (colimMap α) (𝟙 R) ≅ colimit 𝓐` (pushout along iso `colim ιnat ≅ 𝟙 R`,
  -- using `IsConnected I ⟹ colim constR ≅ R`).
  -- Alt elementary route: explicit cocone with apex `colimit 𝓐`, legs
  -- `pushout.desc (colimit.ι 𝓐 i) (colimMap α) (by rw [ι_colimMap])`, shown `IsColimit`
  -- by a universal-property chase, then transport.
  let : Algebra (colimit 𝓡 : CommRingCat).carrier (colimit 𝓐 : CommRingCat).carrier :=
    (colimMap α).hom.toAlgebra
  set R := CommRingCat.of (colimit 𝓡 : CommRingCat).carrier with hR
  -- `I` is filtered (directed + nonempty), hence connected.
  have : IsFiltered I := inferInstance
  have : IsConnected I := IsFiltered.isConnected I
  -- The square `α.app i ≫ colimit.ι 𝓐 i = colimit.ι 𝓡 i ≫ colimMap α`.
  have wsq : ∀ i, α.app i ≫ colimit.ι 𝓐 i = colimit.ι 𝓡 i ≫ colimMap α := fun i =>
    (ι_colimMap α i).symm
  -- Abbreviation for the forgotten diagram `i ↦ pushout (α.app i) (colimit.ι 𝓡 i)`.
  set GF := Gunder I 𝓡 𝓐 α ⋙ Under.forget R with hGF
  -- The transition map `GF.map h` is the `pushout.map` along `(𝓐.map h, 𝟙 R, 𝓡.map h)`.
  -- We record how it interacts with the two pushout legs.
  have hinl : ∀ {i i' : I} (h : i ⟶ i'),
      pushout.inl (α.app i) (colimit.ι 𝓡 i) ≫ GF.map h
        = 𝓐.map h ≫ pushout.inl (α.app i') (colimit.ι 𝓡 i') := by
    intro i i' h
    show pushout.inl (α.app i) (colimit.ι 𝓡 i)
        ≫ (Gunder I 𝓡 𝓐 α ⋙ Under.forget R).map h = _
    simp only [Functor.comp_map, Under.forget_map, Gunder, Under.homMk_right]
    rw [pushout.map, pushout.inl_desc]
  have hinr : ∀ {i i' : I} (h : i ⟶ i'),
      pushout.inr (α.app i) (colimit.ι 𝓡 i) ≫ GF.map h
        = pushout.inr (α.app i') (colimit.ι 𝓡 i') := by
    intro i i' h
    show pushout.inr (α.app i) (colimit.ι 𝓡 i)
        ≫ (Gunder I 𝓡 𝓐 α ⋙ Under.forget R).map h = _
    simp only [Functor.comp_map, Under.forget_map, Gunder, Under.homMk_right]
    rw [pushout.map, pushout.inr_desc, Category.id_comp]
  -- Explicit cocone `D` on `GF` with apex `colimit 𝓐`, legs `pushout.desc`.
  let D : Cocone GF :=
    { pt := colimit 𝓐
      ι :=
        { app := fun i => pushout.desc (colimit.ι 𝓐 i) (colimMap α) (wsq i)
          naturality := by
            intro i i' h
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
            refine pushout.hom_ext ?_ ?_
            · rw [← Category.assoc, hinl h, Category.assoc, pushout.inl_desc,
                pushout.inl_desc, ← colimit.w 𝓐 h]
            · rw [← Category.assoc, hinr h, pushout.inr_desc, pushout.inr_desc] } }
  -- `D` is a colimit cocone, proved via the universal property.
  let hD : IsColimit D :=
    { desc := fun s => colimit.desc 𝓐
        { pt := s.pt
          ι :=
            { app := fun i => pushout.inl (α.app i) (colimit.ι 𝓡 i) ≫ s.ι.app i
              naturality := by
                intro i i' h
                have hnat := s.ι.naturality h
                simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hnat ⊢
                rw [← hnat]
                simp only [← Category.assoc]
                rw [hinl h] } }
      fac := by
        intro s i
        show pushout.desc (colimit.ι 𝓐 i) (colimMap α) (wsq i) ≫ colimit.desc 𝓐 _ = _
        refine pushout.hom_ext ?_ ?_
        · rw [pushout.inl_desc_assoc, colimit.ι_desc]
        · rw [pushout.inr_desc_assoc]
          apply colimit.hom_ext
          intro j
          rw [ι_colimMap_assoc, colimit.ι_desc]
          -- goal: colimit.ι 𝓡 j ≫ pushout.inr ... ≫ s.ι.app i = ... ; use s naturality
          show α.app j ≫ pushout.inl (α.app j) (colimit.ι 𝓡 j) ≫ s.ι.app j
            = colimit.ι 𝓡 j ≫ pushout.inr (α.app i) (colimit.ι 𝓡 i) ≫ s.ι.app i
          -- `pushout.inr` composed with `s.ι` is independent of the index: prove it for `i = j`.
          have hconst : ∀ {a b : I} (h : a ⟶ b),
              pushout.inr (α.app a) (colimit.ι 𝓡 a) ≫ s.ι.app a
                = pushout.inr (α.app b) (colimit.ι 𝓡 b) ≫ s.ι.app b := by
            intro a b h
            have hnat := s.ι.naturality h
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hnat
            rw [← hnat]
            simp only [← Category.assoc]
            rw [hinr h]
          -- Use a common upper bound `k` of `i` and `j`.
          obtain ⟨k, hik, hjk, -⟩ := IsFilteredOrEmpty.cocone_objs i j
          rw [pushout.condition_assoc, hconst hjk, ← hconst hik]
      uniq := by
        intro s m hm
        apply colimit.hom_ext
        intro i
        rw [colimit.ι_desc]
        show colimit.ι 𝓐 i ≫ m = pushout.inl (α.app i) (colimit.ι 𝓡 i) ≫ s.ι.app i
        rw [← hm i]
        show _ = pushout.inl _ _ ≫ pushout.desc (colimit.ι 𝓐 i) (colimMap α) (wsq i) ≫ m
        rw [pushout.inl_desc_assoc] }
  -- `Under.forget R` preserves the colimit of `Gunder`, so its image cocone is a colimit.
  have pres : IsColimit ((Under.forget R).mapCocone (colimit.cocone (Gunder I 𝓡 𝓐 α))) :=
    isColimitOfPreserves (Under.forget R) (colimit.isColimit (Gunder I 𝓡 𝓐 α))
  -- Underlying iso `(colimit Gunder).right ≅ colimit 𝓐`.
  let fUnder : (Under.forget R).obj (colimit (Gunder I 𝓡 𝓐 α)) ≅ colimit 𝓐 :=
    pres.coconePointUniqueUpToIso hD
  -- Assemble the `Under`-iso `colimit Gunder ≅ Under.mk (colimMap α)`.
  let isoUnder : colimit (Gunder I 𝓡 𝓐 α) ≅ Under.mk (colimMap α) :=
    Under.isoMk fUnder (by
      obtain ⟨i⟩ := ‹Nonempty I›
      -- Characterization of `fUnder.hom` from the uniqueness-of-colimit iso.
      have key : (colimit.ι (Gunder I 𝓡 𝓐 α) i).right ≫ fUnder.hom
          = pushout.desc (colimit.ι 𝓐 i) (colimMap α) (wsq i) :=
        pres.comp_coconePointUniqueUpToIso_hom hD i
      -- The structure map of `colimit Gunder` factors through the `i`-th leg.
      have hstruct : (colimit (Gunder I 𝓡 𝓐 α)).hom
          = pushout.inr (α.app i) (colimit.ι 𝓡 i) ≫ (colimit.ι (Gunder I 𝓡 𝓐 α) i).right :=
        (colimit.ι (Gunder I 𝓡 𝓐 α) i).w.symm
      show (colimit (Gunder I 𝓡 𝓐 α)).hom ≫ fUnder.hom = colimMap α
      rw [hstruct, Category.assoc, key, pushout.inr_desc])
  refine ⟨(commAlgCatEquivUnder R).inverse.mapIso isoUnder⟩

/-- **Sub-lemma L_outer (Stacks 0GIM, step 1: colimits commute with tensor).**

With the data of `isFilteredColimitOfEtale_colim` (`R = colimit 𝓡`, `A = colimit 𝓐`, `α : 𝓡 ⟶ 𝓐`),
the `R`-algebra `A` is the filtered colimit, over the directed index `I`, of the
base-changed algebras `A_i ⊗_{R_i} R`. Formally: there is a diagram
`G : I ⥤ CommAlgCat R` with `G.obj i ≅ (the R-algebra A_i ⊗_{R_i} R)` over `R`,
together with a colimit cocone for `G` whose apex is `≅ A = colimit 𝓐` over `R`.

INFORMAL ARGUMENT.
`A = colimit 𝓐 = A ⊗_R R` and `R = colim_i R_i`, so since tensor product commutes
with filtered colimits,
  `A ≅ A ⊗_R R ≅ colim_i (A_i ⊗_{R_i} R)` as `R`-algebras.
Equivalently: `i ↦ (A_i ⊗_{R_i} R)` is the diagram obtained by base-changing the
system `𝓐` along the colimit maps `R_i → R = colimit 𝓡`, and its colimit over the
filtered `I` is `A`. The transition maps of `G` are induced by those of `𝓐` and the
naturality squares of `α`.

The `hG` output — each `G.obj i ≅ A_i ⊗_{R_i} R` is a filtered colimit of étale
`R`-algebras — is supplied by **L_baseChange** (Stacks 0BSH) applied to `hetale i`
(`A_i` is a filtered colimit of étale `R_i`-algebras) along the colimit ring map
`g = colimit.ι 𝓡 i : R_i → R`. This is the ONLY place `hetale` is consumed.

Mathlib inputs: `R = colimit 𝓡` via `colimit.isColimit 𝓡`; the base-change functor
`CommAlgCat R_i ⥤ CommAlgCat R`; that base change along the colimit maps and the
colimit over `I` recover `A` (colimits commute with tensor / left adjoints preserve
colimits, `colimit.isColimit 𝓐`). The directed set `I` is filtered as a category
(`IsFiltered` from `IsDirected` + `Nonempty`). -/
lemma L_outer
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (𝓡 𝓐 : I ⥤ CommRingCat.{u}) (α : 𝓡 ⟶ 𝓐)
    (hetale : ∀ i, IsFilteredColimitOfEtaleHom (α.app i).hom) :
    letI : Algebra (colimit 𝓡 : CommRingCat).carrier (colimit 𝓐 : CommRingCat).carrier :=
      (colimMap α).hom.toAlgebra
    ∃ (G : I ⥤ CommAlgCat.{u} (colimit 𝓡 : CommRingCat).carrier)
      (_ : ∀ i, IsFilteredColimitOfEtaleHom (algebraMap (colimit 𝓡 : CommRingCat).carrier (G.obj
          i)))
      (d : Cocone G),
        Nonempty (d.pt ≅ CommAlgCat.of (colimit 𝓡 : CommRingCat).carrier
            (colimit 𝓐 : CommRingCat).carrier) ∧ Nonempty (IsColimit d) := by
  let : Algebra (colimit 𝓡 : CommRingCat).carrier (colimit 𝓐 : CommRingCat).carrier :=
    (colimMap α).hom.toAlgebra
  exact ⟨Galg I 𝓡 𝓐 α, L_outer_hG I 𝓡 𝓐 α hetale,
    (commAlgCatEquivUnder (CommRingCat.of (colimit 𝓡 : CommRingCat).carrier)).inverse.mapCocone
      (colimit.cocone (Gunder I 𝓡 𝓐 α)),
    L_outer_apex I 𝓡 𝓐 α,
    ⟨isColimitOfPreserves _ (colimit.isColimit (Gunder I 𝓡 𝓐 α))⟩⟩

/-- **Stacks Tag 0GIM, Lemma 10.154.4.**

Let `I` be a directed set (a nonempty directed preorder). Let `𝓡, 𝓐 : I ⥤ CommRingCat`
be two functors (the systems `i ↦ R_i` and `i ↦ A_i`) and `α : 𝓡 ⟶ 𝓐` a natural
transformation (the structure maps `R_i → A_i`, whose naturality squares are the
required commutative squares with the transition maps).

Take colimits `R = colimit 𝓡` and `A = colimit 𝓐`; the induced structure map
`R → A` is `colimMap α`. If each `A_i = 𝓐.obj i` is a filtered colimit of étale
`R_i`-algebras (via the structure map `(α.app i).hom`), then `A` is a filtered
colimit of étale `R`-algebras (via the induced structure map `(colimMap α).hom`). -/
@[stacks 0GIM]
theorem isFilteredColimitOfEtale_colim
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (𝓡 𝓐 : I ⥤ CommRingCat.{u}) (α : 𝓡 ⟶ 𝓐)
    (hetale : ∀ i, IsFilteredColimitOfEtaleHom (α.app i).hom) :
    IsFilteredColimitOfEtaleHom (colimMap α).hom := by
  -- Proof skeleton (Stacks 0GIM), in three stages.
  --
  -- Stage 1 (L_outer / Stacks step 1): exhibit `A = colimit 𝓐`, as an `R`-algebra,
  --   as the filtered colimit over the directed index `I` of the base-changed
  --   algebras `A_i ⊗_{R_i} R`. This produces a diagram `G : I ⥤ CommAlgCat R`
  --   with a colimit cocone `d` of apex `≅ A` over `R`, and — crucially — each
  --   object `G.obj i ≅ A_i ⊗_{R_i} R` is *itself* a filtered colimit of étale
  --   `R`-algebras. The latter "each object is a filtered colimit of étale
  --   R-algebras" fact is L_baseChange (Stacks 0BSH) applied to `hetale i` along
  --   the colimit map `R_i → R`; it is packaged into L_outer's `hG` output.
  --
  -- Stage 2 (L_compose / Stacks 0BSJ): a filtered colimit (over `I`) of objects
  --   each of which is a filtered colimit of étale `R`-algebras is again a
  --   filtered colimit of étale `R`-algebras. Feeding `G`, `d`, its colimit
  --   witness, the iso to `A`, and `hG` into L_compose discharges the goal.
  --
  -- Note `L_outer`'s `hG` hypotheses are supplied by `hetale` via `L_baseChange`;
  -- L_outer is stated to already deliver them so that this assembly is a direct
  -- chain `L_outer → L_compose`.
  obtain ⟨G, hG, d, hiso, ⟨hd⟩⟩ := L_outer I 𝓡 𝓐 α hetale
  exact L_compose (colimMap α).hom I G hG d hd hiso
