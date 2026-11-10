module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleLocallyBijective
public import StacksFrontier.AlgebraicGeometry.Topologies.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.RepresentableSheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of the constant abelian sheaf on the small étale site of a scheme

Let `X` be a scheme and let `A` be an abstract abelian group. The sheafification of the
constant presheaf with value `A` on the small étale site `X.Etale`, taken in the category of
abelian groups, has as its sections over an étale `X`-scheme `V` the group of Zariski locally
constant `A`-valued maps on `V`.

## Main definitions

* `AlgebraicGeometry.locallyConstantMapsAb` — the presheaf of abelian groups on schemes sending
  a scheme to the group of locally constant `A`-valued maps on it.
* `AlgebraicGeometry.smallEtaleLocallyConstantMapsAb` — its restriction to the small étale site
  of a scheme.
* `AlgebraicGeometry.constantToSmallEtaleLocallyConstantMapsAb` — the map of presheaves of
  abelian groups sending `a : A` to the constant map with value `a`.
* `AlgebraicGeometry.smallEtaleConstantSheafIsoLocallyConstantMapsAb` — the identification of
  the constant sheaf of abelian groups on `X.Etale` with the locally constant maps.
* `AlgebraicGeometry.smallEtaleConstantSheafSectionsIsoLocallyConstantMapsAb` — the resulting
  identification of the sections over a single étale `X`-scheme.

## Main results

* `AlgebraicGeometry.smallEtaleConstantSheafIsoLocallyConstantMapsAb_unit`: the identification
  sends the image of `a : A` under the sheafification unit to the constant map with value `a`.
* `AlgebraicGeometry.smallEtaleScheme_openCoverData`: every open cover of an étale `X`-scheme is
  a covering family of the small étale site.
* `AlgebraicGeometry.smallEtaleLocallyConstantMapsAb_isSheaf`: the locally constant maps form a
  sheaf of abelian groups on the small étale site.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry

/-! ### Locally constant maps as a presheaf of abelian groups -/

/-- The presheaf of abelian groups on schemes sending a scheme to the group of locally constant
`A`-valued maps on it, with pullback of functions on morphisms. -/
public def locallyConstantMapsAb (A : Type w) [AddCommGroup A] :
    Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{max u w} where
  obj T := AddCommGrpCat.of (LocallyConstant T.unop A)
  map f := AddCommGrpCat.ofHom (LocallyConstant.comapAddMonoidHom f.unop.base.hom)
  map_id T := by
    ext f x
    rfl
  map_comp f g := by
    ext h x
    rfl

/-- The presheaf of abelian groups on the small étale site of `X` sending an étale `X`-scheme
`V` to the group of locally constant `A`-valued maps on `V`. -/
public abbrev smallEtaleLocallyConstantMapsAb (X : Scheme.{u}) (A : Type w) [AddCommGroup A] :
    (X.Etale)ᵒᵖ ⥤ AddCommGrpCat.{max u w} :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ locallyConstantMapsAb.{u, w} A

/-- For a discrete abelian group `A`, the locally constant `A`-valued maps on a scheme are the
continuous `A`-valued maps on it. -/
public def locallyConstantMapsAbForgetIsoContinuousMaps (A : Type (max (u + 1) v))
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] :
    locallyConstantMapsAb.{u, max (u + 1) v} A ⋙ forget AddCommGrpCat ≅
      continuousMapPresheaf.{max (u + 1) v, u} A := by
  refine NatIso.ofComponents (fun T => Equiv.toIso {
    toFun := fun (f : LocallyConstant T.unop A) => f.toContinuousMap
    invFun := fun (f : C(T.unop, A)) =>
      ⟨(f : T.unop → A), (IsLocallyConstant.iff_continuous (f : T.unop → A)).2 f.continuous⟩
    left_inv := fun f => LocallyConstant.ext (fun _ => rfl)
    right_inv := fun f => ContinuousMap.ext (fun _ => rfl) }) ?_
  intro T₁ T₂ f
  ext g
  exact ContinuousMap.ext fun _ => rfl

/-- Locally constant `A`-valued maps form a presheaf of abelian groups which is an fpqc sheaf on
schemes. -/
public theorem locallyConstantMapsAb_isSheaf_fpqc (A : Type (max (u + 1) v)) [AddCommGroup A] :
    Presheaf.IsSheaf Scheme.fpqcTopology (locallyConstantMapsAb.{u, max (u + 1) v} A) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat) ?_
  exact (Presheaf.isSheaf_of_iso_iff
      (locallyConstantMapsAbForgetIsoContinuousMaps.{u, v} A)).mpr
    (isSheaf_fpqcTopology_continuousMapPresheaf.{max (u + 1) v, u} A)

/-- Locally constant `A`-valued maps form a sheaf of abelian groups for the étale topology on
the schemes over `X`. -/
public theorem locallyConstantMapsAb_isSheaf_etaleOver (X : Scheme.{u})
    (A : Type (max (u + 1) v)) [AddCommGroup A] :
    Presheaf.IsSheaf (Scheme.etaleTopology.{u}.over X)
      ((Over.forget X).op ⋙ locallyConstantMapsAb.{u, max (u + 1) v} A) :=
  Functor.op_comp_isSheaf_of_isSheaf (Over.forget X) _ Scheme.etaleTopology.{u} _
    ((locallyConstantMapsAb_isSheaf_fpqc.{u, v} A).of_le
      Stacks.Sites.etaleTopology_le_fpqcTopology)

/-- Locally constant `A`-valued maps form a sheaf of abelian groups on the small étale site of
a scheme. -/
public theorem smallEtaleLocallyConstantMapsAb_isSheaf (X : Scheme.{u})
    (A : Type (max (u + 1) v)) [AddCommGroup A] :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X)
      (smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} X A) :=
  Functor.op_comp_isSheaf_of_isSheaf (Scheme.Etale.forget X) _
    (Scheme.etaleTopology.{u}.over X) _ (locallyConstantMapsAb_isSheaf_etaleOver.{u, v} X A)

/-! ### Covering data for the small étale site -/

/-- Every open cover of an étale `X`-scheme is a covering family of the small étale site of `X`. -/
public theorem smallEtaleScheme_openCoverData (X : Scheme.{u}) {T : X.Etale}
    (U : T.left → T.left.Opens) (hU : TopologicalSpace.IsOpenCover U) :
    ∃ (I : Type (u + 1)) (W : I → X.Etale) (a : ∀ i, W i ⟶ T) (r : I → T.left),
      Sieve.ofArrows W a ∈ Scheme.smallEtaleTopology X T ∧
        ∀ i y, (Scheme.Etale.forget X ⋙ Over.forget X).map (a i) y ∈ U (r i) := by
  have hsurj : ∀ x : T.left, ∃ i : T.left, x ∈ U i := fun x =>
    TopologicalSpace.Opens.mem_iSup.1 (top_le_iff.2 hU (Set.mem_univ x))
  let I : Type (u + 1) := ULift.{u + 1, u} T.left
  let W : I → X.Etale := fun i => Scheme.Etale.mk ((U i.down).ι ≫ T.hom)
  let a : ∀ i, W i ⟶ T := fun i => MorphismProperty.Over.homMk (U i.down).ι
  refine ⟨I, W, a, fun i => i.down, ?_, ?_⟩
  · refine (Scheme.ofArrows_mem_smallEtaleTopology_iff a).2 ?_
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := hsurj x
    refine Set.mem_iUnion.2 ⟨ULift.up i, ?_⟩
    change x ∈ Set.range (U i).ι.base
    rwa [Scheme.Opens.range_ι]
  · exact fun i y => y.2

/-- Every open cover of an étale `X`-scheme, viewed as a scheme through the forgetful functor,
is a covering family of the small étale site of `X`. -/
public theorem smallEtaleScheme_openCoverData' (X : Scheme.{u}) :
    ∀ {T : X.Etale} (U : (Scheme.Etale.forget X ⋙ Over.forget X).obj T →
      ((Scheme.Etale.forget X ⋙ Over.forget X).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → X.Etale) (a : ∀ i, W i ⟶ T)
        (r : I → (Scheme.Etale.forget X ⋙ Over.forget X).obj T),
        Sieve.ofArrows W a ∈ Scheme.smallEtaleTopology X T ∧
          ∀ i y, (Scheme.Etale.forget X ⋙ Over.forget X).map (a i) y ∈ U (r i) :=
  fun U hU => smallEtaleScheme_openCoverData X U hU

/-- An étale `X`-scheme with empty underlying scheme is covered by the empty family. -/
public theorem smallEtale_bot_mem (X : Scheme.{u}) {T : X.Etale} (hT : IsEmpty T.left) :
    (⊥ : Sieve T) ∈ Scheme.smallEtaleTopology X T :=
  openCoverData_bottom (Scheme.Etale.forget X ⋙ Over.forget X)
    (Scheme.smallEtaleTopology X) (smallEtaleScheme_openCoverData' X) hT

/-! ### The comparison from the constant presheaf -/

/-- The map of presheaves of abelian groups on the small étale site of `X` sending `a : A` to
the constant map with value `a`. -/
public def constantToSmallEtaleLocallyConstantMapsAb (X : Scheme.{u})
    (A : Type (max (u + 1) v)) [AddCommGroup A] :
    (Functor.const (X.Etale)ᵒᵖ).obj (AddCommGrpCat.of A) ⟶
      smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} X A where
  app T := AddCommGrpCat.ofHom (LocallyConstant.constAddMonoidHom (X := T.unop.left))
  naturality T₁ T₂ f := by
    ext a
    rfl

/-- The comparison from the constant presheaf of abelian groups to the presheaf of locally
constant maps is locally injective. -/
public theorem constantToSmallEtaleLocallyConstantMapsAb_isLocallyInjective (X : Scheme.{u})
    (A : Type (max (u + 1) v)) [AddCommGroup A] :
    Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology X)
      (constantToSmallEtaleLocallyConstantMapsAb.{u, v} X A) := by
  classical
  refine ⟨fun {T} a b hab => ?_⟩
  change LocallyConstant.const T.unop.left a = LocallyConstant.const T.unop.left b at hab
  by_cases hT : Nonempty T.unop.left
  · obtain ⟨x⟩ := hT
    obtain rfl : a = b := by
      simpa using congrArg (fun f : LocallyConstant T.unop.left A => f x) hab
    simp
  · by_cases hab' : a = b
    · subst b
      simp
    · have heq : Presheaf.equalizerSieve
          (F := (Functor.const (X.Etale)ᵒᵖ).obj (AddCommGrpCat.of A)) (X := T) a b = ⊥ := by
        ext V f
        simp only [Presheaf.equalizerSieve_apply, Sieve.bot_apply]
        exact ⟨fun hf => hab' (by simpa using hf), False.elim⟩
      rw [heq]
      exact smallEtale_bot_mem X (not_nonempty_iff.mp hT)

/-- The comparison from the constant presheaf of abelian groups to the presheaf of locally
constant maps is locally surjective. -/
public theorem constantToSmallEtaleLocallyConstantMapsAb_isLocallySurjective (X : Scheme.{u})
    (A : Type (max (u + 1) v)) [AddCommGroup A] :
    Presheaf.IsLocallySurjective (Scheme.smallEtaleTopology X)
      (constantToSmallEtaleLocallyConstantMapsAb.{u, v} X A) := by
  classical
  refine ⟨fun {T} s => ?_⟩
  let s₀ : LocallyConstant T.left A := s
  choose O hO hx hconst using s₀.isLocallyConstant.exists_open
  let U : T.left → T.left.Opens := fun x => ⟨O x, hO x⟩
  have hU : TopologicalSpace.IsOpenCover U :=
    top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩
  obtain ⟨I, W, a, r, hcover, hmaps⟩ := smallEtaleScheme_openCoverData X U hU
  refine (Scheme.smallEtaleTopology X).superset_covering (fun V f hf => ?_) hcover
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff W a f).mp hf
  refine (Presheaf.imageSieve
    (constantToSmallEtaleLocallyConstantMapsAb.{u, v} X A) s).downward_closed ?_ g
  refine ⟨s₀ (r i), ?_⟩
  change LocallyConstant.const (W i).left (s₀ (r i)) =
    LocallyConstant.comapAddMonoidHom
      ((Scheme.Etale.forget X ⋙ Over.forget X).map (a i)).base.hom s₀
  refine LocallyConstant.ext fun y => ?_
  change s₀ (r i) = s₀ ((Scheme.Etale.forget X ⋙ Over.forget X).map (a i) y)
  exact (hconst (r i) _ (hmaps i y)).symm

/-! ### The constant abelian sheaf -/

/-- The constant sheaf of abelian groups with value `A` on the small étale site of a scheme `X`
has as its sections over an étale `X`-scheme `V` the group of locally constant `A`-valued maps
on `V`. -/
@[stacks 03P5 "Scheme.smallEtaleTopology with AddCommGrpCat coefficients",
  sga "4 XII 5.6" "special case"]
public def smallEtaleConstantSheafIsoLocallyConstantMapsAb (X : Scheme.{u})
    (A : Type (max (u + 1) v)) [AddCommGroup A] :
    ((constantSheaf (Scheme.smallEtaleTopology X)
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of A)).obj ≅
      smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} X A := by
  let J := Scheme.smallEtaleTopology X
  let α := constantToSmallEtaleLocallyConstantMapsAb.{u, v} X A
  let hP : Presheaf.IsSheaf J (smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} X A) :=
    smallEtaleLocallyConstantMapsAb_isSheaf.{u, v} X A
  have hα : IsIso ((presheafToSheaf J AddCommGrpCat.{max (u + 1) v}).map α) := by
    rw [← J.W_iff]
    exact (J.W_iff_isLocallyBijective α).mpr
      ⟨constantToSmallEtaleLocallyConstantMapsAb_isLocallyInjective.{u, v} X A,
        constantToSmallEtaleLocallyConstantMapsAb_isLocallySurjective.{u, v} X A⟩
  let P := (Functor.const (X.Etale)ᵒᵖ).obj (AddCommGrpCat.of A)
  let L : Sheaf J AddCommGrpCat.{max (u + 1) v} := ⟨_, hP⟩
  let e₁ : (constantSheaf J AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of A) ≅
      (presheafToSheaf J AddCommGrpCat.{max (u + 1) v}).obj P := Iso.refl _
  let e₂ : (presheafToSheaf J AddCommGrpCat.{max (u + 1) v}).obj P ≅
      (presheafToSheaf J AddCommGrpCat.{max (u + 1) v}).obj
        (smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} X A) :=
    asIso ((presheafToSheaf J AddCommGrpCat.{max (u + 1) v}).map α)
  let e₃ : (presheafToSheaf J AddCommGrpCat.{max (u + 1) v}).obj
      (smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} X A) ≅ L :=
    asIso ((sheafificationAdjunction J AddCommGrpCat.{max (u + 1) v}).counit.app L)
  simpa [P, L, α] using (Functor.mapIso (sheafToPresheaf J AddCommGrpCat.{max (u + 1) v})
    ((e₁.trans e₂).trans e₃))

/-- The identification of the constant abelian sheaf on the small étale site with the locally
constant maps sends the sheafification-unit image of `a : A` to the constant map with value
`a`. -/
@[stacks 03P5 "constant sections on Scheme.smallEtaleTopology, AddCommGrpCat coefficients"]
public theorem smallEtaleConstantSheafIsoLocallyConstantMapsAb_unit (X : Scheme.{u})
    (A : Type (max (u + 1) v)) [AddCommGroup A] (T : (X.Etale)ᵒᵖ) (a : A) :
    ((smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v} X A).hom.app T)
      ((toSheafify (Scheme.smallEtaleTopology X)
        ((Functor.const (X.Etale)ᵒᵖ).obj (AddCommGrpCat.of A))).app T a) =
      LocallyConstant.const T.unop.left a := by
  let J := Scheme.smallEtaleTopology X
  let α := constantToSmallEtaleLocallyConstantMapsAb.{u, v} X A
  let hP : Presheaf.IsSheaf J (smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} X A) :=
    smallEtaleLocallyConstantMapsAb_isSheaf.{u, v} X A
  change (sheafifyLift J α hP).app T
    (((toSheafify J ((Functor.const (X.Etale)ᵒᵖ).obj (AddCommGrpCat.of A))).app T) a) = _
  exact congrArg (fun f => f.app T a) (toSheafify_sheafifyLift J α hP)

/-- The sections of the constant abelian sheaf with value `A` over a single étale `X`-scheme
`V` are the locally constant `A`-valued maps on `V`. -/
@[sga "4 XII 5.6" "special case"]
public def smallEtaleConstantSheafSectionsIsoLocallyConstantMapsAb (X : Scheme.{u})
    (A : Type (max (u + 1) v)) [AddCommGroup A] (V : X.Etale) :
    ((constantSheaf (Scheme.smallEtaleTopology X)
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of A)).obj.obj (op V) ≅
      AddCommGrpCat.of (LocallyConstant V.left A) :=
  (smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v} X A).app (op V)

end AlgebraicGeometry

end
