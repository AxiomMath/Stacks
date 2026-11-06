module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.ContActionForget
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Defs
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Exactness
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of Galois categories

An exact functor between Galois categories, equipped with fibre functors, induces a continuous
homomorphism between their automorphism groups. The corresponding equivalences with categories
of finite continuous group actions form a 2-commutative square. The homomorphism is canonical up
to inner conjugacy, and every continuous homomorphism arises in this way.

## Main definitions

* `CategoryTheory.setValuedFiberFunctor` is the bridge from finite-set-valued fibre functors to
  the type-valued fibre functors in `CategoryTheory.IsGaloisCategory`.
* `CategoryTheory.inducedHom` is transport of natural automorphisms along a functor and an
  isomorphism of fibre functors.
* `CategoryTheory.GaloisFunctorData` packages the induced continuous homomorphism and the
  2-commutative square.
* `CategoryTheory.IsInnerConjugate` says that two homomorphisms differ by an inner automorphism
  of the target.
* `CategoryTheory.ExactFunctorInducingData` packages the converse construction and all its
  specifications.

## Main results

* `CategoryTheory.fiberIsoOfExact` chooses the required isomorphism of fibre functors.
* `CategoryTheory.galoisFunctorDataOfFiberIso` constructs the continuous homomorphism and
  2-commutative square for each choice of that isomorphism.
* `CategoryTheory.galoisFunctorData_hom_innerConjugate` gives independence of the fibre-functor
  isomorphism up to inner conjugacy.
* `CategoryTheory.exactFunctorInducingData` constructs an exact functor inducing a prescribed
  continuous homomorphism.

## Implementation notes

Fibre functors are taken with values in `FintypeCat`; the named bridge
`setValuedFiberFunctor F = F ⋙ FintypeCat.incl` gives the set-valued fibre functor appearing in
the definition of a Galois category. This lets the 2-commutative square use Mathlib's canonical
functors to finite continuous actions directly. The underlying map on automorphism groups is
explicitly conjugation by the chosen fibre-functor isomorphism, and the underlying component of
the displayed 2-isomorphism is its inverse. Parameterizing `GaloisFunctorData` by that chosen
isomorphism records that every choice produces the asserted continuous homomorphism and square;
`GaloisFunctorData.hom_toMonoidHom` and `GaloisFunctorData.actionIso_hom_app` are the two
specification lemmas. In the converse construction, `ExactFunctorInducingData.exact` and
`ExactFunctorInducingData.hom_eq` specify exactness and recovery of the supplied homomorphism.

## References

* [Stacks Project, Tag 0BN5](https://stacks.math.columbia.edu/tag/0BN5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete CategoryTheory.PreGaloisCategory

universe u v u' v' w

namespace CategoryTheory

universe uX vX wX
variable {D : Type uX} [Category.{vX, uX} D]

private theorem mono_split_from_connected_decomp (F : D ⥤ Type wX)
    [hG : IsGaloisCategory F] {X Y : D} (i : X ⟶ Y) [Mono i] :
    ∃ (Z : D) (uX : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i uX)) := by
  classical
  let : HasFiniteLimits D := hG.hasFiniteLimits
  let : HasFiniteColimits D := hG.hasFiniteColimits
  let : PreservesFiniteLimits F := hG.exact.1
  let : PreservesFiniteColimits F := hG.exact.2
  obtain ⟨ι, A, f, hc, hfin, hconn⟩ := hG.exists_finite_coproduct_connected Y
  let P (j : ι) := pullback i (f j)
  let S : Set ι := {j : ι | IsEmpty (F.obj (P j))}
  let J := {j : ι // j ∈ S}
  let : Finite J := Finite.of_injective (fun j : J => j.1) Subtype.val_injective
  let Z : D := colimit (Discrete.functor (fun j : J => A j.1))
  let uX : Z ⟶ Y := Sigma.desc fun j : J => f j.1
  let g : X ⨿ Z ⟶ Y := coprod.desc i uX
  let eYcofan : Cofan (fun j : ι => F.obj (A j)) :=
    Cofan.mk (F.obj Y) (fun j => F.map (f j))
  have heYcofan : IsColimit eYcofan :=
    Cofan.isColimitMapCoconeEquiv F A (Cofan.mk Y f) (isColimitOfPreserves F hc)
  let eY : (Σ j : ι, F.obj (A j)) ≃ F.obj Y :=
    CofanTypes.equivOfIsColimit ((Cofan.isColimit_cofanTypes_iff eYcofan).2 ⟨heYcofan⟩)
  have eY_apply (j : ι) (a : F.obj (A j)) : eY ⟨j, a⟩ = F.map (f j) a := rfl
  let eZcofan : Cofan (fun j : J => F.obj (A j.1)) :=
    Cofan.mk (F.obj Z) (fun j => F.map (Sigma.ι (fun j : J => A j.1) j))
  have heZcofan : IsColimit eZcofan :=
    Cofan.isColimitMapCoconeEquiv F (fun j : J => A j.1)
      (Cofan.mk Z (fun j => Sigma.ι (fun j : J => A j.1) j))
      (isColimitOfPreserves F (coproductIsCoproduct (fun j : J => A j.1)))
  let eZ : (Σ j : J, F.obj (A j.1)) ≃ F.obj Z :=
    CofanTypes.equivOfIsColimit ((Cofan.isColimit_cofanTypes_iff eZcofan).2 ⟨heZcofan⟩)
  let eXZ : F.obj X ⊕ F.obj Z ≅ F.obj (X ⨿ Z) :=
    (Types.binaryCoproductIso (F.obj X) (F.obj Z)).symm ≪≫ PreservesColimitPair.iso F X Z
  let m : F.obj X ⊕ F.obj Z → F.obj Y := fun z => F.map g (eXZ.hom z)
  have eXZ_inl (x : F.obj X) : (eXZ.hom) (Sum.inl x) = F.map coprod.inl x := by
    show (↾Sum.inl ≫ eXZ.hom) x = _
    have hh : (↾Sum.inl) ≫ eXZ.hom = F.map coprod.inl := by
      dsimp [eXZ]
      rw [← Category.assoc, Types.binaryCoproductIso_inl_comp_inv]
      exact coprodComparison_inl (F := F) (A := X) (B := Z)
    rw [hh]
  have eXZ_inr (z : F.obj Z) : (eXZ.hom) (Sum.inr z) = F.map coprod.inr z := by
    show (↾Sum.inr ≫ eXZ.hom) z = _
    have hh : (↾Sum.inr) ≫ eXZ.hom = F.map coprod.inr := by
      dsimp [eXZ]
      rw [← Category.assoc, Types.binaryCoproductIso_inr_comp_inv]
      exact coprodComparison_inr (F := F) (A := X) (B := Z)
    rw [hh]
  have hm_inl (x : F.obj X) : m (Sum.inl x) = F.map i x := by
    show F.map g (eXZ.hom (Sum.inl x)) = _
    rw [eXZ_inl, ← ConcreteCategory.comp_apply, ← F.map_comp, coprod.inl_desc]
  have hm_inr (z : F.obj Z) : m (Sum.inr z) = F.map uX z := by
    show F.map g (eXZ.hom (Sum.inr z)) = _
    rw [eXZ_inr, ← ConcreteCategory.comp_apply, ← F.map_comp, coprod.inr_desc]
  have hu_component (j : J) (a : F.obj (A j.1)) :
      F.map uX (F.map (Sigma.ι (fun j : J => A j.1) j) a) = F.map (f j.1) a := by
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, Sigma.ι_desc]
  have hm_component (j : J) (a : F.obj (A j.1)) :
      m (Sum.inr (F.map (Sigma.ι (fun j : J => A j.1) j) a)) = eY ⟨j.1, a⟩ := by
    rw [hm_inr, hu_component, eY_apply]
  have pullbackEquiv (j : ι) : F.obj (P j) ≃
      {q : F.obj X × F.obj (A j) // F.map i q.1 = F.map (f j) q.2} :=
    (PreservesPullback.iso F i (f j) ≪≫
      Types.pullbackIsoPullback (F.map i) (F.map (f j))).toEquiv
  have pullback_nonempty (j : ι) (x : F.obj X) (a : F.obj (A j))
      (h : F.map i x = F.map (f j) a) : Nonempty (F.obj (P j)) :=
    ⟨(pullbackEquiv j).symm ⟨(x, a), h⟩⟩
  have snd_iso_of_nonempty (j : ι) (hp : Nonempty (F.obj (P j))) :
      IsIso (pullback.snd i (f j)) := by
    apply hconn j |>.noTrivialComponent (P j) (pullback.snd i (f j))
    intro hinit
    have hempty := (isInitial_iff_isEmpty_fiber F (P j)).mp ⟨hinit⟩
    exact hempty.false (Classical.choice hp)
  have hz_repr (z : F.obj Z) : ∃ (j : J) (a : F.obj (A j.1)),
      F.map (Sigma.ι (fun j : J => A j.1) j) a = z :=
    ⟨(eZ.symm z).1, (eZ.symm z).2, eZ.apply_symm_apply z⟩
  have hm_inl_ne_inr (x : F.obj X) (z : F.obj Z) : m (Sum.inl x) ≠ m (Sum.inr z) := by
    intro hst
    obtain ⟨j, a, rfl⟩ := hz_repr z
    exact j.2.false (Classical.choice (pullback_nonempty j.1 x a
      ((hm_inl x).symm.trans (hst.trans (hm_component j a)))))
  have hm_injective : Function.Injective m := by
    rintro (x | z) (y | z') hst
    · have hinj : Function.Injective (F.map i) :=
        (CategoryTheory.mono_iff_injective (F.map i)).mp (Functor.map_mono F i)
      exact congrArg Sum.inl (hinj (by simpa [hm_inl] using hst))
    · exact (hm_inl_ne_inr x z' hst).elim
    · exact (hm_inl_ne_inr y z hst.symm).elim
    · obtain ⟨j, a, rfl⟩ := hz_repr z
      obtain ⟨k, b, rfl⟩ := hz_repr z'
      have hsig : (⟨j.1, a⟩ : Σ j : ι, F.obj (A j)) = ⟨k.1, b⟩ :=
        eY.injective ((hm_component j a).symm.trans (hst.trans (hm_component k b)))
      obtain rfl : j = k := Subtype.ext (congrArg Sigma.fst hsig)
      cases hsig
      rfl
  have hm_surjective : Function.Surjective m := by
    intro y
    let q := eY.symm y
    by_cases hq : q.1 ∈ S
    · let j : J := ⟨q.1, hq⟩
      refine ⟨Sum.inr (F.map (Sigma.ι (fun j : J => A j.1) j) q.2), ?_⟩
      rw [hm_component]
      show eY ⟨q.1, q.2⟩ = y
      exact eY.apply_symm_apply y
    · have hp : Nonempty (F.obj (P q.1)) := not_isEmpty_iff.mp hq
      let hs := snd_iso_of_nonempty q.1 hp
      let p := F.map (inv (pullback.snd i (f q.1))) q.2
      have hp_snd : F.map (pullback.snd i (f q.1)) p = q.2 := by
        simp [p]
      refine ⟨Sum.inl (F.map (pullback.fst i (f q.1)) p), ?_⟩
      calc
        m (Sum.inl (F.map (pullback.fst i (f q.1)) p)) =
            F.map i (F.map (pullback.fst i (f q.1)) p) := hm_inl _
        _ = F.map (f q.1) q.2 := by
          simpa [Functor.map_comp, hp_snd] using
            congrArg (fun k => F.map k p) (pullback.condition (f := i) (g := f q.1))
        _ = eY q := (eY_apply q.1 q.2).symm
        _ = y := eY.apply_symm_apply y
  have hbij : Function.Bijective (F.map g) := by
    constructor
    · exact fun x y hxy ↦ eXZ.toEquiv.symm.injective (hm_injective (by simpa [m] using hxy))
    · intro y
      obtain ⟨z, hz⟩ := hm_surjective y
      exact ⟨eXZ.toEquiv z, by simpa [m] using hz⟩
  have hgisom : IsIso (F.map g) := (ConcreteCategory.isIso_iff_bijective (F.map g)).mpr hbij
  have : IsIso g := isIso_of_reflects_iso g F
  let c₂ : BinaryCofan X Z := BinaryCofan.mk coprod.inl coprod.inr
  let c₁ : BinaryCofan X Z := BinaryCofan.mk i uX
  let eG : (X ⨿ Z) ≅ Y := Iso.mk g (inv g) (IsIso.hom_inv_id g) (IsIso.inv_hom_id g)
  let eC : c₂ ≅ c₁ := Cocone.ext eG (by
    rintro (_ | _)
    · exact coprod.inl_desc i uX
    · exact coprod.inr_desc i uX)
  exact ⟨Z, uX, ⟨IsColimit.ofIsoColimit (coprodIsCoprod X Z) eC⟩⟩

/-- A finite-set-valued functor whose composite with the inclusion satisfies the Galois category
axioms is a fibre functor. -/
private theorem fiberFunctor_of_isGaloisCategory (F : D ⥤ FintypeCat.{wX})
    [hG : IsGaloisCategory (F ⋙ FintypeCat.incl)] [PreGaloisCategory D] :
    PreGaloisCategory.FiberFunctor F := by
  let : PreservesFiniteLimits (F ⋙ FintypeCat.incl) := hG.exact.1
  let : PreservesFiniteColimits (F ⋙ FintypeCat.incl) := hG.exact.2
  let : PreservesFiniteLimits F :=
    preservesFiniteLimits_of_reflects_of_preserves F FintypeCat.incl
  let : PreservesFiniteColimits F :=
    preservesFiniteColimits_of_reflects_of_preserves F FintypeCat.incl
  refine {
    preservesQuotientsByFiniteGroups := fun G _ _ => by
      obtain ⟨G', hg, hfin, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{vX, 0} G
      let : Fintype G' := Fintype.ofFinite G'
      exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm F
    reflectsIsos := by
      constructor
      intro X Y f hf
      have hfG : IsIso ((F ⋙ FintypeCat.incl).map f) := FintypeCat.incl.map_isIso (F.map f)
      exact isIso_of_reflects_iso f (F ⋙ FintypeCat.incl)
  }

/-- The axioms of `IsGaloisCategory` imply Mathlib's `CategoryTheory.GaloisCategory`. -/
public lemma IsGaloisCategory.toGaloisCategory (F : D ⥤ Type wX) [hG : IsGaloisCategory F] :
    CategoryTheory.GaloisCategory D := by
  let : HasFiniteLimits D := hG.hasFiniteLimits
  let : HasFiniteColimits D := hG.hasFiniteColimits
  let : PreGaloisCategory D := {
    hasTerminal := inferInstance
    hasPullbacks := inferInstance
    hasFiniteCoproducts := inferInstance
    hasQuotientsByFiniteGroups := fun G _ _ => by
      obtain ⟨G', hg, hfin, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{vX, 0} G
      exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm
    monoInducesIsoOnDirectSummand := by
      intro X Y i hi
      exact mono_split_from_connected_decomp F i
  }
  let F' : D ⥤ FintypeCat.{wX} := ObjectProperty.lift _ F (fun X => hG.finite_obj X)
  have hF' : F' ⋙ FintypeCat.incl = F := rfl
  have : IsGaloisCategory (F' ⋙ FintypeCat.incl) := hG
  let : PreGaloisCategory.FiberFunctor F' := fiberFunctor_of_isGaloisCategory F'
  let Fv : D ⥤ FintypeCat.{vX} := F' ⋙ FintypeCat.uSwitch.{wX, vX}
  let : PreGaloisCategory.FiberFunctor Fv := PreGaloisCategory.FiberFunctor.comp_right _
  exact ⟨⟨Fv, inferInstance⟩⟩

/-- A finite-set-valued functor whose composite with the inclusion satisfies the Galois category
axioms is a fibre functor in Mathlib's sense. -/
@[sga "1 V 5.1" "An exact"]
public lemma IsGaloisCategory.fiberFunctor (F : D ⥤ FintypeCat.{wX})
    [hG : IsGaloisCategory (F ⋙ FintypeCat.incl)] [PreGaloisCategory D] :
    PreGaloisCategory.FiberFunctor F :=
  fiberFunctor_of_isGaloisCategory F

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

/-- The type-valued fibre functor underlying a finite-set-valued fibre functor. -/
public abbrev setValuedFiberFunctor (F : C ⥤ FintypeCat.{w}) : C ⥤ Type w :=
  F ⋙ FintypeCat.incl

/-- The homomorphism on automorphism groups obtained by precomposition with `H` and transport
along an isomorphism `H ⋙ F' ≅ F` of fibre functors. -/
public def inducedHom (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w}) (H : C ⥤ C')
    (t : H ⋙ F' ≅ F) : Aut F' →* Aut F :=
  t.conjAut.toMonoidHom.comp
    (((Functor.whiskeringLeft C C' FintypeCat).obj H).mapAut F')

/-- The data expressing functoriality of the equivalence between a Galois category and finite
continuous actions for a fixed isomorphism of fibre functors.  The last field fixes the
2-isomorphism canonically over that chosen isomorphism. -/
public structure GaloisFunctorData (F : C ⥤ FintypeCat.{w})
    (F' : C' ⥤ FintypeCat.{w}) (H : C ⥤ C') (fiberIso : H ⋙ F' ≅ F) where
  /-- The induced continuous homomorphism of automorphism groups. -/
  hom : Aut F' →ₜ* Aut F
  /-- The underlying homomorphism is transport of structure along `fiberIso`. -/
  hom_toMonoidHom : hom.toMonoidHom = inducedHom F F' H fiberIso
  /-- The 2-isomorphism between the two routes around the functoriality square. -/
  actionIso :
    PreGaloisCategory.functorToContAction F ⋙ ContAction.res FintypeCat hom ≅
      H ⋙ PreGaloisCategory.functorToContAction F'
  /-- After forgetting the actions, the component of `actionIso` is `fiberIso.inv`. -/
  actionIso_hom_app (X : C) : (actionIso.hom.app X).hom.hom = fiberIso.inv.app X

/-- Two group homomorphisms are inner conjugate if one is obtained from the other by conjugating
all values by a fixed element of the target group. -/
public def IsInnerConjugate {G' G : Type*} [Group G'] [Group G]
    (h₁ h₂ : G' →* G) : Prop :=
  ∃ g : G, ∀ x : G', h₂ x = g * h₁ x * g⁻¹

private lemma aut_conjAut_eq_inner {C : Type uX} [Category.{vX, uX} C] {X : C}
    (g a : Aut X) : g.asIso.conjAut a = g * a * g⁻¹ := by
  apply Aut.ext
  simp [Iso.conjAut_apply]

private def liftFiberIso {C : Type u} [Category.{v} C]
    {A B : C ⥤ FintypeCat.{w}}
    (e : A ⋙ FintypeCat.incl ≅ B ⋙ FintypeCat.incl) : A ≅ B := by
  refine NatIso.ofComponents (fun X => FintypeCat.equivEquivIso (e.app X).toEquiv) ?_
  exact fun f ↦ FintypeCat.incl.map_injective (e.hom.naturality f)

/-- An exact functor between Galois categories admits an isomorphism of fibre functors. -/
@[stacks 0BN5 "existence of the fibre-functor isomorphism",
  sga "1 V 6.2" "existence of t",
  sga "1 V 6.3" "U(F')=F'∘H lies in Γ", sga "1 V 5.7" "more general"]
public theorem nonempty_fiberIso_of_exact
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (hH : exactFunctor C C' H) :
    Nonempty (H ⋙ F' ≅ F) := by
  let : CategoryTheory.GaloisCategory C :=
    IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F)
  let : CategoryTheory.GaloisCategory C' :=
    IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F')
  let : PreGaloisCategory.FiberFunctor F := IsGaloisCategory.fiberFunctor F
  let : PreGaloisCategory.FiberFunctor F' := IsGaloisCategory.fiberFunctor F'
  let E := Functor.asEquivalence (PreGaloisCategory.functorToContAction F)
  let E' := Functor.asEquivalence (PreGaloisCategory.functorToContAction F')
  have hE'functor : E'.functor = PreGaloisCategory.functorToContAction F' := rfl
  let : E.inverse.IsEquivalence := Equivalence.isEquivalence_inverse E
  let : E'.functor.IsEquivalence := by infer_instance
  let : HasFiniteLimits (ContAction FintypeCat.{w} (Aut F)) := by infer_instance
  let : HasFiniteColimits (ContAction FintypeCat.{w} (Aut F)) := by infer_instance
  let : HasFiniteLimits (ContAction FintypeCat.{w} (Aut F')) := by infer_instance
  let : HasFiniteColimits (ContAction FintypeCat.{w} (Aut F')) := by infer_instance
  let : PreservesFiniteLimits E.inverse := by infer_instance
  let : PreservesFiniteColimits E.inverse := by infer_instance
  let : PreservesFiniteLimits E'.functor := by infer_instance
  let : PreservesFiniteColimits E'.functor := by infer_instance
  let K := E.inverse ⋙ H ⋙ E'.functor
  let : PreservesFiniteLimits H := hH.1
  let : PreservesFiniteColimits H := hH.2
  let : PreservesFiniteLimits (H ⋙ E'.functor) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (H ⋙ E'.functor) := comp_preservesFiniteColimits _ _
  let : PreservesFiniteLimits K := comp_preservesFiniteLimits E.inverse (H ⋙ E'.functor)
  let : PreservesFiniteColimits K := comp_preservesFiniteColimits E.inverse (H ⋙ E'.functor)
  let : PreservesFiniteLimits FintypeCat.incl := by infer_instance
  let : PreservesFiniteColimits FintypeCat.incl := by infer_instance
  let : PreservesFiniteLimits
      (forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat ⋙ FintypeCat.incl) :=
    comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits
      (forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat ⋙ FintypeCat.incl) :=
    comp_preservesFiniteColimits _ _
  let : PreservesFiniteLimits
      (K ⋙ (forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat ⋙ FintypeCat.incl)) :=
    comp_preservesFiniteLimits K _
  let : PreservesFiniteColimits
      (K ⋙ (forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat ⋙ FintypeCat.incl)) :=
    comp_preservesFiniteColimits K _
  let : ∀ X : ContAction FintypeCat.{w} (Aut F),
      Finite ((K ⋙ forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat ⋙
        FintypeCat.incl).obj X) := by
    intro X
    exact (forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat).obj (K.obj X) |>.property
  let θ := Classical.choice (nonempty_iso_forget_of_preservesFiniteLimits_and_colimits
    (K ⋙ forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat ⋙ FintypeCat.incl))
  let θFiniteShape := Functor.associator K
      (forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat) FintypeCat.incl ≪≫ θ
  let θForLift := θFiniteShape ≪≫ (forget₂InclIso (G := Aut F)).symm
  let θFin := liftFiberIso θForLift
  let θFin' := Functor.isoWhiskerLeft E.functor θFin
  have hUnit : H ⋙ F' ≅ E.functor ⋙ K ⋙
      forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat := by
    calc
      H ⋙ F' ≅ (E.functor ⋙ E.inverse) ⋙ H ⋙ F' := by
        simpa only [Functor.id_comp] using Functor.isoWhiskerRight E.unitIso (H ⋙ F')
      _ ≅ E.functor ⋙ E.inverse ⋙ H ⋙ E'.functor ⋙
          forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat := by
        simpa only [Functor.assoc, hE'functor] using
          Functor.isoWhiskerLeft (E.functor ⋙ E.inverse ⋙ H) (actionForgetFinIso F').symm
      _ ≅ E.functor ⋙ K ⋙
          forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat := Iso.refl _
  have hForget : E.functor ⋙
      forget₂ (ContAction FintypeCat.{w} (Aut F)) FintypeCat ≅ F := actionForgetFinIso F
  exact ⟨hUnit ≪≫ θFin' ≪≫ hForget.symm⟩

/-- A chosen isomorphism between the composite fibre functor of an exact functor and the original
fibre functor. -/
public noncomputable def fiberIsoOfExact
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (hH : exactFunctor C C' H) : H ⋙ F' ≅ F :=
  Classical.choice (nonempty_fiberIso_of_exact F F' H hH)

/-- For every chosen isomorphism of fibre functors, transport of structure gives a continuous
homomorphism and a 2-isomorphism between the two routes around the finite-action square. -/
@[stacks 0BN5 "continuous homomorphism and 2-commutative square"]
public theorem nonempty_galoisFunctorData_of_fiberIso
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) :
    Nonempty (GaloisFunctorData F F' H t) := by
  let h : Aut F' →ₜ* Aut F := {
    toMonoidHom := inducedHom F F' H t
    continuous_toFun := by
      rw [Topology.IsInducing.continuous_iff
        (PreGaloisCategory.autEmbedding_isClosedEmbedding F).isInducing,
        continuous_pi_iff]
      intro X
      have heval : Continuous (fun σ : Aut F' =>
          CategoryTheory.PreGaloisCategory.autEmbedding F' σ (H.obj X)) :=
        (continuous_apply (H.obj X)).comp continuous_induced_dom
      have hconj : Continuous (fun a : Aut (F'.obj (H.obj X)) => (t.app X).conjAut a) :=
        continuous_of_discreteTopology
      show Continuous (fun σ : Aut F' => (t.app X).conjAut
        (CategoryTheory.PreGaloisCategory.autEmbedding F' σ (H.obj X)))
      exact hconj.comp heval
  }
  let α : PreGaloisCategory.functorToContAction F ⋙ ContAction.res FintypeCat h ≅
      H ⋙ PreGaloisCategory.functorToContAction F' := by
    refine NatIso.ofComponents (fun X => ?_) (fun f => ?_)
    · refine ObjectProperty.isoMk _ (Action.mkIso (t.app X).symm ?_)
      intro g
      show (inducedHom F F' H t g).asIso.hom.app X ≫ t.inv.app X =
        t.inv.app X ≫ g.asIso.hom.app (H.obj X)
      simp [inducedHom, Iso.conjAut_hom, Iso.conj_apply, Functor.mapAut]
    · apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      simp only [ContAction.res, ObjectProperty.lift, Action.res, Functor.comp_map]
      exact t.inv.naturality f
  refine ⟨⟨h, rfl, α, ?_⟩⟩
  intro X
  simp [α, Action.mkIso]
  rfl

/-- The functoriality data determined by a specified isomorphism of fibre functors. -/
public noncomputable def galoisFunctorDataOfFiberIso
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) :
    GaloisFunctorData F F' H t :=
  Classical.choice (nonempty_galoisFunctorData_of_fiberIso F F' H t)

/-- The functoriality data obtained from the chosen fibre-functor isomorphism of an exact
functor. -/
@[sga "1 V 6.3" "partial"]
public noncomputable def galoisFunctorDataOfExact
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (hH : exactFunctor C C' H) :
    GaloisFunctorData F F' H (fiberIsoOfExact F F' H hH) :=
  galoisFunctorDataOfFiberIso F F' H (fiberIsoOfExact F F' H hH)

/-- The homomorphisms obtained from two choices of fibre-functor isomorphism differ by an inner
automorphism of the target automorphism group. -/
@[stacks 0BN5 "independence up to inner conjugacy", sga "1 V 6.2" "h indep. of t"]
public theorem galoisFunctorData_hom_innerConjugate
    {F : C ⥤ FintypeCat.{w}} {F' : C' ⥤ FintypeCat.{w}} {H : C ⥤ C'}
    {t₁ t₂ : H ⋙ F' ≅ F} (d₁ : GaloisFunctorData F F' H t₁)
    (d₂ : GaloisFunctorData F F' H t₂) :
    IsInnerConjugate d₁.hom.toMonoidHom d₂.hom.toMonoidHom := by
  let g : Aut F := .of (t₁.symm ≪≫ t₂)
  refine ⟨g, fun x => ?_⟩
  rw [d₂.hom_toMonoidHom, d₁.hom_toMonoidHom]
  show t₂.conjAut
      (((Functor.whiskeringLeft C C' FintypeCat).obj H).mapAut F' x) =
    g *
      (t₁.conjAut (((Functor.whiskeringLeft C C' FintypeCat).obj H).mapAut F' x)) *
      g⁻¹
  have ht : t₂ = t₁ ≪≫ g.asIso := by cat_disch
  rw [ht, Iso.trans_conjAut]
  exact aut_conjAut_eq_inner g _

/-- An exact functor, an isomorphism of fibre functors, and the functoriality data recovering a
specified continuous homomorphism. -/
public structure ExactFunctorInducingData
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w}) (h : Aut F' →ₜ* Aut F) where
  /-- The functor induced by `h`. -/
  functor : C ⥤ C'
  /-- The induced functor is exact. -/
  exact : exactFunctor C C' functor
  /-- The isomorphism between its composite fibre functor and `F`. -/
  fiberIso : functor ⋙ F' ≅ F
  /-- The continuous homomorphism and 2-commutative square associated to `fiberIso`. -/
  data : GaloisFunctorData F F' functor fiberIso
  /-- Transport of structure through `fiberIso` recovers the prescribed homomorphism. -/
  hom_eq : data.hom = h

/-- Every continuous homomorphism between the automorphism groups of two Galois fibre functors is
induced by an exact functor and an isomorphism of fibre functors. -/
@[stacks 0BN5 "converse construction",
  sga "1 V 6.2" "converse direction",
  sga "1 V 6.3" "essential surjectivity"]
public theorem nonempty_exactFunctorInducingData
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (h : Aut F' →ₜ* Aut F) :
    Nonempty (ExactFunctorInducingData F F' h) := by
  let : CategoryTheory.GaloisCategory C :=
    IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F)
  let : CategoryTheory.GaloisCategory C' :=
    IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F')
  let : PreGaloisCategory.FiberFunctor F := IsGaloisCategory.fiberFunctor F
  let : PreGaloisCategory.FiberFunctor F' := IsGaloisCategory.fiberFunctor F'
  let E := Functor.asEquivalence (PreGaloisCategory.functorToContAction F)
  let E' := Functor.asEquivalence (PreGaloisCategory.functorToContAction F')
  let : E.functor.IsEquivalence := by infer_instance
  let : E'.inverse.IsEquivalence := Equivalence.isEquivalence_inverse E'
  let : PreservesFiniteLimits E.functor := by infer_instance
  let : PreservesFiniteColimits E.functor := by infer_instance
  let : PreservesFiniteLimits E'.inverse := by infer_instance
  let : PreservesFiniteColimits E'.inverse := by infer_instance
  let R := ContAction.res FintypeCat h
  let U := forget₂ (ContAction FintypeCat.{w} (Aut F)) FintypeCat
  let U' := forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat
  let : PreservesFiniteLimits (R ⋙ U') :=
    preservesFiniteLimits_of_natIso (restrictionForgetFinIso h).symm
  let : PreservesFiniteColimits (R ⋙ U') :=
    preservesFiniteColimits_of_natIso (restrictionForgetFinIso h).symm
  let : PreservesFiniteLimits R := preservesFiniteLimits_of_reflects_of_preserves R U'
  let : PreservesFiniteColimits R := preservesFiniteColimits_of_reflects_of_preserves R U'
  let H := E.functor ⋙ R ⋙ E'.inverse
  let : PreservesFiniteLimits (R ⋙ E'.inverse) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (R ⋙ E'.inverse) := comp_preservesFiniteColimits _ _
  have hHexact : exactFunctor C C' H :=
    ⟨comp_preservesFiniteLimits E.functor (R ⋙ E'.inverse),
      comp_preservesFiniteColimits E.functor (R ⋙ E'.inverse)⟩
  let t : H ⋙ F' ≅ F := by
    refine NatIso.ofComponents (fun X => ?_) ?_
    · show F'.obj (E'.inverse.obj (R.obj (E.functor.obj X))) ≅ F.obj X
      exact U'.mapIso (E'.counitIso.app (R.obj (E.functor.obj X)))
    · intro X Y f
      exact congrArg (fun g => U'.map g)
        (E'.counitIso.hom.naturality (R.map (E.functor.map f)))
  let d := Classical.choice (nonempty_galoisFunctorData_of_fiberIso F F' H t)
  refine ⟨⟨H, hHexact, t, d, ?_⟩⟩
  apply ContinuousMonoidHom.ext
  intro a
  show d.hom.toMonoidHom a = h.toMonoidHom a
  rw [d.hom_toMonoidHom]
  apply Aut.ext
  ext X x
  let A := R.obj (E.functor.obj X)
  let c := E'.counitIso.app A
  let y := (U'.mapIso c).inv.hom x
  change ((E'.inverse ⋙ E'.functor).obj A).obj.V at y
  show ConcreteCategory.hom (c.hom.hom.hom)
      (ConcreteCategory.hom (((E'.inverse ⋙ E'.functor).obj A).obj.ρ a).asHom y) =
    ((h a).asIso.hom.app X).hom x
  rw [← FintypeCat.comp_apply, ConcreteCategory.congr_hom (c.hom.hom.comm a) y,
    FintypeCat.comp_apply]
  have hy : ConcreteCategory.hom (c.hom.hom.hom) y = x := by
    show ConcreteCategory.hom (U'.mapIso c).hom.hom y = x
    exact ConcreteCategory.congr_hom ((U'.mapIso c).inv_hom_id) x
  rw [hy]
  show ConcreteCategory.hom ((E.functor.obj X).obj.ρ (h a)).asHom x = (h a).asIso.hom.app X x
  show (h a) • x = (h a).asIso.hom.app X x
  exact PreGaloisCategory.mulAction_def F (h a) x

/-- The exact functor and fibre-functor isomorphism induced by a specified continuous
homomorphism, packaged with their specifications. -/
public noncomputable def exactFunctorInducingData
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (h : Aut F' →ₜ* Aut F) : ExactFunctorInducingData F F' h :=
  Classical.choice (nonempty_exactFunctorInducingData F F' h)

end CategoryTheory
