module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-compact opens of a base change to an algebra

Let `k` be a commutative ring, let `X` be a scheme over `k` and let `A` be a `k`-algebra. A
quasi-compact open of the base change `X_A` already lives over a finitely generated
`k`-subalgebra of `A`: it is the inverse image of a quasi-compact open of `X_{A'}` for some
finitely generated `k`-subalgebra `A' ⊆ A`.

The proof is the one the source remarks on: `A` is the filtered colimit of its finitely
generated `k`-subalgebras, so `X_A` is the cofiltered limit of the base changes `X_{A'}`, whose
transition morphisms are affine, and a quasi-compact open of such a limit descends to a stage by
[Stacks, Tag 01Z4] part (1). No quasi-separatedness of `X` is needed, so the remark of the
source that the quasi-separated case follows from Tag 01Z4 applies in general here.

## Main definitions

Nothing in this file is exported except the result below. The limit presentation it runs on is
private to the file: `AlgebraicGeometry.FGSubalgebra` is the index of finitely generated
`k`-subalgebras of `A`, `AlgebraicGeometry.subalgebraCocone` is the tautological cocone of those
subalgebras with apex `A`, and `AlgebraicGeometry.baseChangeLimitCone` is the resulting limit
cone of base changes with apex `X_A`.

## Main results

* `AlgebraicGeometry.exists_fg_subalgebra_descending_isCompact_open` is **[Stacks, Tag 0388]**:
  descent of a quasi-compact open of `X_A` to a finitely generated `k`-subalgebra.

## Implementation notes

The base change `X_A` is `pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f`, the fibre
product with `Spec A` as the *first* factor, which is the order the source uses when it writes
`X_A = Spec(A) ×_{Spec(k)} X`. Taking it in that order is what makes the apex of the limit cone
be `X_A` on the nose, by `rfl`, so the descended open is transported by no isomorphism at all
and the morphism `X_A ⟶ X_{A'}` produced is literally a leg of the limit cone.

The morphism `X_A ⟶ X_{A'}` is pinned down in the statement by its two projections, rather than
being named: it is the unique morphism commuting with the projection to `X` and covering
`Spec A ⟶ Spec A'`. This is the form [Stacks, Tag 04KU] part (1) takes in
`AlgebraicGeometry.exists_finite_subextension_descending_isCompact_open`, which is the same
statement for an algebraic field extension in place of `A`.

The source states this for `k` a field; neither the statement nor the proof uses more than that
`k` is a commutative ring, so that is the hypothesis imposed.

The limit presentation is a generalisation of the one
`StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit` carries publicly, which asks `A` to
be a field extension of `k`. It is kept private here rather than being exported as a second
public copy of that API; the declarations of that file are not touched.

## References

* [Stacks Project, Tag 0388](https://stacks.math.columbia.edu/tag/0388)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 04KU](https://stacks.math.columbia.edu/tag/04KU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The finitely generated `k`-subalgebras of a `k`-algebra `A`, ordered by inclusion. These are
exactly the `k`-subalgebras of finite type, by `Subalgebra.fg_iff_finiteType`. -/
private abbrev FGSubalgebra (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] :=
  {B : Subalgebra k A // B.FG}

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The zero subalgebra is finitely generated, so the index is nonempty. -/
private instance : Nonempty (FGSubalgebra k A) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- Two finitely generated subalgebras are contained in a third, namely their join. -/
private instance : IsDirected (FGSubalgebra k A) (· ≤ ·) :=
  ⟨fun i j => ⟨⟨i.1 ⊔ j.1, i.2.sup j.2⟩,
    Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩⟩

/-- The diagram of finitely generated `k`-subalgebras of `A` and the inclusions between them. -/
private def subalgebraDiagram : FGSubalgebra k A ⥤ CommAlgCat.{u} k where
  obj i := CommAlgCat.of k i.1
  map {i j} h := CommAlgCat.ofHom (Subalgebra.inclusion h.le)
  map_id i := by apply CommAlgCat.hom_ext; ext x; rfl
  map_comp {i j l} h g := by apply CommAlgCat.hom_ext; ext x; rfl

/-- The cocone on the diagram of finitely generated subalgebras whose apex is `A` itself, with
legs the inclusions into `A`. -/
private def subalgebraCocone : Cocone (subalgebraDiagram k A) where
  pt := CommAlgCat.of k A
  ι :=
    { app := fun i => CommAlgCat.ofHom (Subalgebra.val i.1)
      naturality := by intro i j h; apply CommAlgCat.hom_ext; ext x; rfl }

/-- The finitely generated `k`-subalgebras of `A` form a directed family. -/
private theorem directed_coe :
    Directed (· ≤ ·) (fun i : FGSubalgebra k A => (i : Subalgebra k A)) := by
  intro i j
  obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
  exact ⟨l, hil, hjl⟩

/-- Every element of `A` lies in a finitely generated `k`-subalgebra, namely the one it
generates. -/
private theorem exists_mem_fgSubalgebra (x : A) :
    ∃ i : FGSubalgebra k A, x ∈ (i : Subalgebra k A) :=
  ⟨⟨Algebra.adjoin k ({x} : Set A),
      (Subalgebra.fg_iff_finiteType _).2
        (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x))⟩,
    Algebra.subset_adjoin rfl⟩

/-- The finitely generated `k`-subalgebras of `A` have supremum `A`. -/
private theorem iSup_coe_eq_top : (⨆ i : FGSubalgebra k A, (i : Subalgebra k A)) = ⊤ :=
  le_antisymm le_top fun x _ => by
    obtain ⟨i, hi⟩ := exists_mem_fgSubalgebra k A x
    exact le_iSup (fun i : FGSubalgebra k A => (i : Subalgebra k A)) i hi

/-- The leg of a cocone at a stage, read as an algebra map out of the subalgebra itself. -/
private def leg (c : Cocone (subalgebraDiagram k A)) (i : FGSubalgebra k A) :
    (i : Subalgebra k A) →ₐ[k] ToType c.pt :=
  (c.ι.app i).hom

/-- The legs of a cocone agree along an inclusion of subalgebras. -/
private theorem leg_inclusion {c : Cocone (subalgebraDiagram k A)} {i j : FGSubalgebra k A}
    (h : (i : Subalgebra k A) ≤ (j : Subalgebra k A)) (x : (i : Subalgebra k A)) :
    leg k A c j (Subalgebra.inclusion h x) = leg k A c i x :=
  congrArg (fun q : CommAlgCat.Hom ((subalgebraDiagram k A).obj i) c.pt => q.hom x)
    (c.w (homOfLE (Subtype.coe_le_coe.mp h)))

/-- The compatibility of the legs of a cocone in the shape `Subalgebra.iSupLift` asks for. -/
private theorem leg_comp_inclusion (c : Cocone (subalgebraDiagram k A)) :
    ∀ (i j : FGSubalgebra k A) (h : (i : Subalgebra k A) ≤ (j : Subalgebra k A)),
      leg k A c i = (leg k A c j).comp (Subalgebra.inclusion h) :=
  fun _ _ h => AlgHom.ext fun x => (leg_inclusion k A h x).symm

/-- The algebra map out of `A` determined by a cocone on the diagram of finitely generated
`k`-subalgebras: every element of `A` lies in some stage, and the legs agree on overlaps. -/
private noncomputable def liftAlg (c : Cocone (subalgebraDiagram k A)) :
    A →ₐ[k] ToType c.pt :=
  (Subalgebra.iSupLift (fun i : FGSubalgebra k A => (i : Subalgebra k A)) (directed_coe k A)
      (leg k A c) (leg_comp_inclusion k A c) ⊤ (iSup_coe_eq_top k A).symm.le).comp
    Subalgebra.topEquiv.symm.toAlgHom

/-- The map out of `A` determined by a cocone restricts on a stage to the leg there. -/
private theorem liftAlg_coe (c : Cocone (subalgebraDiagram k A)) (i : FGSubalgebra k A)
    (x : (i : Subalgebra k A)) : liftAlg k A c (x : A) = leg k A c i x :=
  Subalgebra.iSupLift_mk (K := fun i : FGSubalgebra k A => (i : Subalgebra k A))
    (dir := directed_coe k A) (f := leg k A c) (hf := leg_comp_inclusion k A c) (T := ⊤) x trivial

/-- A `k`-algebra is the filtered colimit of its finitely generated `k`-subalgebras. -/
private noncomputable def isColimitSubalgebraCocone : IsColimit (subalgebraCocone k A) where
  desc c := CommAlgCat.ofHom (liftAlg k A c)
  fac c i := by apply CommAlgCat.hom_ext; ext x; exact liftAlg_coe k A c i x
  uniq c m hm := by
    apply CommAlgCat.hom_ext
    ext x
    obtain ⟨i, hi⟩ := exists_mem_fgSubalgebra k A x
    refine (ConcreteCategory.congr_hom (hm i) (⟨x, hi⟩ : (i : Subalgebra k A))).trans ?_
    exact (liftAlg_coe k A c i ⟨x, hi⟩).symm

/-- The cofiltered diagram of the spectra of the finitely generated `k`-subalgebras of `A`, as
schemes over `Spec k`. -/
private noncomputable def specDiagram : (FGSubalgebra k A)ᵒᵖ ⥤ Over (Spec (.of k)) :=
  (subalgebraDiagram k A).op ⋙ algSpec (CommRingCat.of k)

/-- `Spec A` is the limit of the spectra of the finitely generated `k`-subalgebras of `A`, over
`Spec k`, because `Spec` on algebras preserves limits. -/
private noncomputable def specLimitCone : LimitCone (specDiagram k A) where
  cone := (algSpec (CommRingCat.of k)).mapCone (subalgebraCocone k A).op
  isLimit :=
    haveI : PreservesLimitsOfSize.{u, u} (algSpec (CommRingCat.of k)) :=
      preservesLimitsOfSize_algSpec
    isLimitOfPreserves _ (isColimitSubalgebraCocone k A).op

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The diagram of base changes `i ↦ Spec Aᵢ ×_{Spec k} X` of `X` to the finitely generated
`k`-subalgebras of `A`. -/
private noncomputable def baseChangeDiagram : (FGSubalgebra k A)ᵒᵖ ⥤ Scheme.{u} :=
  specDiagram k A ⋙ Over.pullback f ⋙ Over.forget X

/-- `X_A` is the limit of the base changes of `X` to the finitely generated `k`-subalgebras of
`A`: base change along `f` is a right adjoint and the forgetful functor from the slice category
preserves cofiltered limits. The apex is `X_A` on the nose. -/
private noncomputable def baseChangeLimitCone : LimitCone (baseChangeDiagram k A f) where
  cone := (Over.forget X).mapCone ((Over.pullback f).mapCone (specLimitCone k A).cone)
  isLimit :=
    haveI : PreservesLimitsOfShape (FGSubalgebra k A)ᵒᵖ (Over.forget X) := inferInstance
    isLimitOfPreserves _ (isLimitOfPreserves _ (specLimitCone k A).isLimit)

/-- The transition morphisms of the diagram of base changes are affine, being base changes of
the morphisms of spectra induced by the inclusions of subalgebras. -/
private instance isAffineHom_baseChangeDiagram_map {i j : (FGSubalgebra k A)ᵒᵖ} (g : i ⟶ j) :
    IsAffineHom ((baseChangeDiagram k A f).map g) := by
  refine MorphismProperty.overPullbackMap (P := @IsAffineHom) f ((specDiagram k A).map g) ?_
  change IsAffineHom (Spec.map _)
  infer_instance

/-- A leg of the limit cone covers the morphism `Spec A ⟶ Spec Aᵢ` induced by the inclusion of
the subalgebra. -/
private theorem baseChangeLimitCone_π_comp_fst (i : (FGSubalgebra k A)ᵒᵖ) :
    (baseChangeLimitCone k A f).cone.π.app i ≫
        pullback.fst ((specDiagram k A).obj i).hom f =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) f ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.val (i.unop : Subalgebra k A)).toRingHom) := by
  exact pullback.lift_fst _ _ _

/-- A leg of the limit cone commutes with the projection to `X`. -/
private theorem baseChangeLimitCone_π_comp_snd (i : (FGSubalgebra k A)ᵒᵖ) :
    (baseChangeLimitCone k A f).cone.π.app i ≫
        pullback.snd ((specDiagram k A).obj i).hom f =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) f := by
  exact pullback.lift_snd _ _ _

/-- **[Stacks, Tag 0388].** Let `X` be a scheme over a commutative ring `k` and let `A` be a
`k`-algebra. A quasi-compact open `V` of the base change `X_A` is the inverse image of a
quasi-compact open `V'` of `X_{A'}` for some finitely generated `k`-subalgebra `A' ⊆ A`.

The morphism `X_A ⟶ X_{A'}` along which `V'` is pulled back is characterised by its two
projections: it covers the morphism `Spec A ⟶ Spec A'` induced by the inclusion `A' ⊆ A` and it
commutes with the projection to `X`. -/
@[stacks 0388, ega "IV 8.2.11" "X_A over f.g. subalgs"]
public theorem exists_fg_subalgebra_descending_isCompact_open
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (V : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f).Opens)
    (hV : IsCompact V.1) :
    ∃ (A' : Subalgebra k A) (_ : A'.FG)
      (V' : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A'))) f).Opens),
      IsCompact V'.1 ∧
        ∃ p : pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f ⟶
              pullback (Spec.map (CommRingCat.ofHom (algebraMap k A'))) f,
          p ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A'))) f =
              pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) f ≫
                Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom) ∧
            p ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A'))) f =
              pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) f ∧
            V = p ⁻¹ᵁ V' := by
  obtain ⟨i, V', hV', hVeq⟩ := AlgebraicGeometry.exists_preimage_eq
    (baseChangeDiagram k A f) (baseChangeLimitCone k A f).cone
    (baseChangeLimitCone k A f).isLimit V hV
  exact ⟨(i.unop : Subalgebra k A), i.unop.2, V', hV',
    (baseChangeLimitCone k A f).cone.π.app i, baseChangeLimitCone_π_comp_fst k A f i,
    baseChangeLimitCone_π_comp_snd k A f i, hVeq.symm⟩

end AlgebraicGeometry

end
