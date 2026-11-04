module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Jacobson.Ring

/-!
# A field extension as a limit of finite-type base changes

Let `k` be a field, `K/k` a field extension and `X` a scheme over `k`. Write `K = colim Aᵢ` as the
filtered colimit of the `k`-subalgebras of `K` of finite type over `k` and put
`Xᵢ = X ×_{Spec k} Spec Aᵢ`. Then `X_K = lim Xᵢ` is the limit of a cofiltered system of schemes
with affine transition morphisms. This file constructs that presentation, as in the proofs of
[Stacks, Tag 0BDC], [Stacks, Tag 0BDD] and [Stacks, Tag 0BDE].

## Main definitions

* `AlgebraicGeometry.FieldExtensionDescent.FGSubalgebra`: the finitely generated `k`-subalgebras of
  `K`, ordered by inclusion.
* `AlgebraicGeometry.FieldExtensionDescent.subalgebraDiagram` and `subalgebraCocone`: the diagram
  of those subalgebras in `CommAlgCat k` and the cocone on it with apex `K`.
* `AlgebraicGeometry.FieldExtensionDescent.specDiagram`: the induced cofiltered diagram of spectra,
  as schemes over `Spec k`.
* `AlgebraicGeometry.FieldExtensionDescent.baseChangeDiagram`: the diagram
  `i ↦ X ×_{Spec k} Spec Aᵢ`.

## Main results

* `AlgebraicGeometry.FieldExtensionDescent.isColimitSubalgebraCocone`: `K` is the filtered colimit
  of its finitely generated `k`-subalgebras.
* `AlgebraicGeometry.FieldExtensionDescent.specLimitCone`: `Spec K` is the limit of the spectra of
  those subalgebras, over `Spec k`.
* `AlgebraicGeometry.FieldExtensionDescent.baseChangeLimitCone` and `baseChangeLimitCone_pt`: `X_K`
  is the limit of the base changes `Xᵢ`, the apex being the fibre product
  `pullback (Spec.map (algebraMap k K)) f` on the nose.
* `AlgebraicGeometry.FieldExtensionDescent.isAffineHom_baseChangeDiagram_map`: the transition
  morphisms of that diagram are affine.
* `AlgebraicGeometry.FieldExtensionDescent.compactSpace_baseChangeDiagram_obj` and
  `quasiSeparatedSpace_baseChangeDiagram_obj`: each stage is quasi-compact and quasi-separated as
  soon as `X` is.
* `AlgebraicGeometry.FieldExtensionDescent.finite_quotient_of_isMaximal`: the residue field of a
  stage at a maximal ideal is a finite extension of `k` ([Stacks, Tag 00FV]).

## Implementation notes

The scheme-level cones are transported from the colimit of algebras: `AlgebraicGeometry.algSpec`
preserves limits, `CategoryTheory.Over.pullback f` is a right adjoint, and
`CategoryTheory.Over.forget` preserves cofiltered limits.

## References

* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
* [Stacks Project, Tag 0BDD](https://stacks.math.columbia.edu/tag/0BDD)
* [Stacks Project, Tag 0BDE](https://stacks.math.columbia.edu/tag/0BDE)
* [Stacks Project, Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FieldExtensionDescent

/-- The finitely generated `k`-subalgebras of a field extension `K/k`, ordered by inclusion. These
are exactly the `k`-subalgebras of finite type, by `Subalgebra.fg_iff_finiteType`. -/
public abbrev FGSubalgebra (k K : Type u) [Field k] [Field K] [Algebra k K] :=
  {A : Subalgebra k K // A.FG}

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- There is a finitely generated `k`-subalgebra of `K`, namely `⊥`. -/
public instance : Nonempty (FGSubalgebra k K) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- Two finitely generated subalgebras are contained in a third, namely their join. -/
public instance : IsDirected (FGSubalgebra k K) (· ≤ ·) :=
  ⟨fun i j => ⟨⟨i.1 ⊔ j.1, i.2.sup j.2⟩,
    Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩⟩

/-- The diagram of finitely generated `k`-subalgebras of `K` and the inclusions between them. -/
@[simps]
public def subalgebraDiagram : FGSubalgebra k K ⥤ CommAlgCat.{u} k where
  obj i := CommAlgCat.of k i.1
  map {i j} h := CommAlgCat.ofHom (Subalgebra.inclusion h.le)
  map_id i := by apply CommAlgCat.hom_ext; ext x; rfl
  map_comp {i j l} h g := by apply CommAlgCat.hom_ext; ext x; rfl

/-- The cocone on the diagram of finitely generated subalgebras whose apex is `K` itself, with legs
the inclusions into `K`. -/
@[simps]
public def subalgebraCocone : Cocone (subalgebraDiagram k K) where
  pt := CommAlgCat.of k K
  ι :=
    { app := fun i => CommAlgCat.ofHom (Subalgebra.val i.1)
      naturality := by intro i j h; apply CommAlgCat.hom_ext; ext x; rfl }

/-- The finitely generated `k`-subalgebras of `K` form a directed family. -/
public theorem directed_coe :
    Directed (· ≤ ·) (fun i : FGSubalgebra k K => (i : Subalgebra k K)) :=
  fun i j => exists_ge_ge i j

/-- Every element of `K` lies in a finitely generated `k`-subalgebra, namely the one it
generates. -/
public theorem exists_mem (x : K) : ∃ i : FGSubalgebra k K, x ∈ (i : Subalgebra k K) :=
  ⟨⟨Algebra.adjoin k ({x} : Set K),
      (Subalgebra.fg_iff_finiteType _).2
        (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x))⟩,
    Algebra.subset_adjoin rfl⟩

/-- The finitely generated `k`-subalgebras of `K` have supremum `K`. -/
public theorem iSup_coe_eq_top : (⨆ i : FGSubalgebra k K, (i : Subalgebra k K)) = ⊤ :=
  le_antisymm le_top fun x _ => by
    obtain ⟨i, hi⟩ := exists_mem k K x
    exact le_iSup (fun i : FGSubalgebra k K => (i : Subalgebra k K)) i hi

/-- The leg of a cocone at a stage, read as an algebra map out of the subalgebra itself. -/
public def leg (c : Cocone (subalgebraDiagram k K)) (i : FGSubalgebra k K) :
    (i : Subalgebra k K) →ₐ[k] ToType c.pt :=
  (c.ι.app i).hom

/-- The legs of a cocone agree along an inclusion of subalgebras. -/
public theorem leg_inclusion {c : Cocone (subalgebraDiagram k K)} {i j : FGSubalgebra k K}
    (h : (i : Subalgebra k K) ≤ (j : Subalgebra k K)) (x : (i : Subalgebra k K)) :
    leg k K c j (Subalgebra.inclusion h x) = leg k K c i x :=
  congrArg (fun q : CommAlgCat.Hom ((subalgebraDiagram k K).obj i) c.pt => q.hom x)
    (c.w (homOfLE (Subtype.coe_le_coe.mp h)))

/-- The legs of a cocone, as algebra maps, commute with the inclusions of subalgebras. -/
public theorem leg_comp_inclusion (c : Cocone (subalgebraDiagram k K)) :
    ∀ (i j : FGSubalgebra k K) (h : (i : Subalgebra k K) ≤ (j : Subalgebra k K)),
      leg k K c i = (leg k K c j).comp (Subalgebra.inclusion h) :=
  fun _ _ h => AlgHom.ext fun x => (leg_inclusion k K h x).symm

/-- The algebra map out of `K` determined by a cocone on the diagram of finitely generated
`k`-subalgebras. -/
public noncomputable def liftAlg (c : Cocone (subalgebraDiagram k K)) :
    K →ₐ[k] ToType c.pt :=
  (Subalgebra.iSupLift (fun i : FGSubalgebra k K => (i : Subalgebra k K)) (directed_coe k K)
      (leg k K c) (leg_comp_inclusion k K c) ⊤ (iSup_coe_eq_top k K).symm.le).comp
    Subalgebra.topEquiv.symm.toAlgHom

/-- `liftAlg` agrees with the leg of the cocone on each finitely generated subalgebra. -/
@[simp] public theorem liftAlg_coe (c : Cocone (subalgebraDiagram k K)) (i : FGSubalgebra k K)
    (x : (i : Subalgebra k K)) : liftAlg k K c (x : K) = leg k K c i x :=
  Subalgebra.iSupLift_mk (K := fun i : FGSubalgebra k K => (i : Subalgebra k K))
    (dir := directed_coe k K) (f := leg k K c) (hf := leg_comp_inclusion k K c) (T := ⊤) x trivial

/-- `K` is the filtered colimit of its finitely generated `k`-subalgebras. -/
public noncomputable def isColimitSubalgebraCocone : IsColimit (subalgebraCocone k K) where
  desc c := CommAlgCat.ofHom (liftAlg k K c)
  fac c i := by apply CommAlgCat.hom_ext; ext x; exact liftAlg_coe k K c i x
  uniq c m hm := by
    apply CommAlgCat.hom_ext
    ext x
    obtain ⟨i, hi⟩ := exists_mem k K x
    refine (ConcreteCategory.congr_hom (hm i) (⟨x, hi⟩ : (i : Subalgebra k K))).trans ?_
    exact (liftAlg_coe k K c i ⟨x, hi⟩).symm

/-- The cofiltered diagram of the spectra of the finitely generated `k`-subalgebras of `K`, as
schemes over `Spec k`. -/
public noncomputable def specDiagram : (FGSubalgebra k K)ᵒᵖ ⥤ Over (Spec (.of k)) :=
  (subalgebraDiagram k K).op ⋙ algSpec (CommRingCat.of k)

/-- `Spec K` is the limit of the spectra of the finitely generated `k`-subalgebras of `K`, over
`Spec k`. -/
public noncomputable def specLimitCone : LimitCone (specDiagram k K) where
  cone := (algSpec (CommRingCat.of k)).mapCone (subalgebraCocone k K).op
  isLimit :=
    haveI : PreservesLimitsOfSize.{u, u} (algSpec (CommRingCat.of k)) :=
      preservesLimitsOfSize_algSpec
    isLimitOfPreserves _ (isColimitSubalgebraCocone k K).op

/-- The structure morphism of a stage of the spectral diagram is the morphism of spectra induced by
the inclusion of the subalgebra. -/
public theorem specDiagram_obj_hom (i : (FGSubalgebra k K)ᵒᵖ) :
    ((specDiagram k K).obj i).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (i.unop : Subalgebra k K))) :=
  rfl

/-- The structure morphism of a stage of the spectral diagram is affine. -/
public instance isAffineHom_specDiagram_hom (i : (FGSubalgebra k K)ᵒᵖ) :
    IsAffineHom ((specDiagram k K).obj i).hom := by
  change IsAffineHom (Spec.map _)
  infer_instance

/-- The structure morphism of a stage of the spectral diagram is quasi-separated. -/
public instance quasiSeparated_specDiagram_hom (i : (FGSubalgebra k K)ᵒᵖ) :
    QuasiSeparated ((specDiagram k K).obj i).hom := by
  change QuasiSeparated (Spec.map _)
  infer_instance

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The diagram of base changes `i ↦ X ×_{Spec k} Spec Aᵢ` of `X` to the finitely generated
`k`-subalgebras of `K`. -/
public noncomputable def baseChangeDiagram : (FGSubalgebra k K)ᵒᵖ ⥤ Scheme.{u} :=
  specDiagram k K ⋙ Over.pullback f ⋙ Over.forget X

/-- `X_K` is the limit of the base changes of `X` to the finitely generated `k`-subalgebras of
`K`. -/
public noncomputable def baseChangeLimitCone : LimitCone (baseChangeDiagram k K f) where
  cone := (Over.forget X).mapCone ((Over.pullback f).mapCone (specLimitCone k K).cone)
  isLimit := isLimitOfPreserves _ (isLimitOfPreserves _ (specLimitCone k K).isLimit)

/-- The apex of `baseChangeLimitCone` is, definitionally, the base change
`pullback (Spec.map (algebraMap k K)) f` of `X` to `K`. -/
public theorem baseChangeLimitCone_pt : (baseChangeLimitCone k K f).cone.pt =
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f :=
  rfl

/-- A stage of the base-changed diagram is the fibre product of `X` with the spectrum of the
subalgebra. -/
public theorem baseChangeDiagram_obj (i : (FGSubalgebra k K)ᵒᵖ) :
    (baseChangeDiagram k K f).obj i =
      pullback ((specDiagram k K).obj i).hom f :=
  rfl

/-- The transition morphisms of the base-changed diagram are affine. -/
public instance isAffineHom_baseChangeDiagram_map {i j : (FGSubalgebra k K)ᵒᵖ} (g : i ⟶ j) :
    IsAffineHom ((baseChangeDiagram k K f).map g) := by
  refine MorphismProperty.overPullbackMap (P := @IsAffineHom) f ((specDiagram k K).map g) ?_
  change IsAffineHom (Spec.map _)
  infer_instance

/-- Each stage of the base-changed diagram is affine over `X`. -/
public instance isAffineHom_baseChangeStage (i : (FGSubalgebra k K)ᵒᵖ) :
    IsAffineHom (pullback.snd ((specDiagram k K).obj i).hom f) :=
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) f :=
    ⟨fun sq H => isAffineHom_isStableUnderBaseChange.of_isPullback sq H⟩
  MorphismProperty.pullback_snd _ _ inferInstance

/-- Each stage of the base-changed diagram is quasi-separated over `X`. -/
public instance quasiSeparated_baseChangeStage (i : (FGSubalgebra k K)ᵒᵖ) :
    QuasiSeparated (pullback.snd ((specDiagram k K).obj i).hom f) :=
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@QuasiSeparated) f :=
    ⟨fun sq H => quasiSeparated_isStableUnderBaseChange.of_isPullback sq H⟩
  MorphismProperty.pullback_snd _ _ inferInstance

/-- Each stage of the base-changed diagram has quasi-compact underlying space as soon as `X`
does. -/
public instance compactSpace_baseChangeDiagram_obj [CompactSpace X] (i : (FGSubalgebra k K)ᵒᵖ) :
    CompactSpace ((baseChangeDiagram k K f).obj i) :=
  inferInstanceAs (CompactSpace (pullback ((specDiagram k K).obj i).hom f : Scheme.{u}))

/-- Each stage of the base-changed diagram has quasi-separated underlying space as soon as `X`
does. -/
public instance quasiSeparatedSpace_baseChangeDiagram_obj [QuasiSeparatedSpace X]
    (i : (FGSubalgebra k K)ᵒᵖ) : QuasiSeparatedSpace ((baseChangeDiagram k K f).obj i) :=
  letI : QuasiSeparatedSpace (pullback ((specDiagram k K).obj i).hom f : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd ((specDiagram k K).obj i).hom f)
  inferInstanceAs
    (QuasiSeparatedSpace (pullback ((specDiagram k K).obj i).hom f : Scheme.{u}))

/-- A finitely generated `k`-subalgebra of `K` is of finite type over `k`. -/
public instance finiteType_coe (i : FGSubalgebra k K) :
    Algebra.FiniteType k (i : Subalgebra k K) :=
  (Subalgebra.fg_iff_finiteType _).1 i.2

/-- The residue field of a finitely generated `k`-subalgebra of `K` at a maximal ideal is a finite
extension of `k` (Zariski's lemma, [Stacks, Tag 00FV]). -/
public theorem finite_quotient_of_isMaximal (i : FGSubalgebra k K)
    (m : Ideal (i : Subalgebra k K)) [m.IsMaximal] :
    Module.Finite k ((i : Subalgebra k K) ⧸ m) :=
  let : Field ((i : Subalgebra k K) ⧸ m) := Ideal.Quotient.field m
  let : Algebra.FiniteType k ((i : Subalgebra k K) ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  finite_of_finite_type_of_isJacobsonRing k ((i : Subalgebra k K) ⧸ m)

end AlgebraicGeometry.FieldExtensionDescent

end
