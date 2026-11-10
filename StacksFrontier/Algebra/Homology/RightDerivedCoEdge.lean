module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.Algebra.Homology.RightDerivedEdge

/-!
# The co-edge morphism of a composite of right derived functors

Let `P : A ⥤ B` and `Q : B ⥤ D` be additive functors between abelian categories with enough
injectives, let `P` preserve injective objects, and let `Q` be *left exact*.  There is then a
canonical morphism

  `Rⁿ (Q ∘ P) X ⟶ Q (Rⁿ P X)`,

natural in `X`.  It is the edge morphism `H^n ⟶ E₂^{0,n}` of the Grothendieck spectral sequence
of the pair `(P, Q)`, and in the geometric case `P = f_*`, `Q = Γ(Y, -)` it is the map
`H^n(X, F) ⟶ Γ(Y, Rⁿ f_* F)` which sends a cohomology class to its induced global section of the
higher direct image.  Together with
`Stacks.Cohomology.RightDerivedEdge.edge` it makes up the two nontrivial maps of the five-term
exact sequence of [Stacks, Tag 01F2].

The construction is a two-step comparison on an injective resolution `I` of `X`.  Write
`K = P I`, a cochain complex in `B`.  Left exactness of `Q` makes the canonical comparison
`Q (Zⁿ K) ⟶ Zⁿ (Q K)` an isomorphism, because both sides are kernels of `Q` applied to the same
differential (`mapCycles`, `isIso_mapCycles`).  The homology `Hⁿ (Q K)` is a cokernel of
`Zⁿ (Q K)`'s boundary inclusion, so a morphism out of it is the same thing as a morphism out of
`Zⁿ (Q K)` killing the boundaries, and `Q` applied to the projection `Zⁿ K ⟶ Hⁿ K` is such a
morphism; this gives `homologyToMapHomology`.  Transporting along
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` on both ends turns it into the natural
transformation `secondEdge`.

Nothing here needs the comparison theorem for injective resolutions: the two ends of
`secondEdge` are right derived functors of `P ⋙ Q` and of `P`, computed on *the same*
resolution, so a single `InjectiveResolution.desc` serves both and no homotopy uniqueness
statement is invoked.

## Main definitions

* `Stacks.Cohomology.RightDerivedCoEdge.mapCycles`: the comparison `Q (Zⁿ C) ⟶ Zⁿ (Q C)`,
  an isomorphism when `Q` preserves finite limits.
* `Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology`: the comparison
  `Hⁿ (Q C) ⟶ Q (Hⁿ C)` for a left exact `Q`.
* `Stacks.Cohomology.RightDerivedCoEdge.secondEdge`: the co-edge morphism
  `(P ⋙ Q).rightDerived n ⟶ P.rightDerived n ⋙ Q`.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.secondEdge_app_eq`: *any* injective resolution computes
  the co-edge morphism.  This is the characterisation consumers use, since it frees them from the
  globally chosen resolutions.
* `Stacks.Cohomology.RightDerivedCoEdge.edge_comp_secondEdge`: the first edge morphism followed
  by the co-edge morphism vanishes in every positive degree.
* `Stacks.Cohomology.RightDerivedCoEdge.mono_edge_app_one`: the *first* edge morphism
  `Stacks.Cohomology.RightDerivedEdge.edge` is a monomorphism in degree one when `P` is left
  exact.  This is the injectivity of `H¹(Y, f_* F) ⟶ H¹(X, F)`.

The second half of the file proves that injectivity, and needs only two degrees of the
resolutions and no spectral sequence.  Left exactness of `P` makes `0 ⟶ P X ⟶ (P I)⁰ ⟶ (P I)¹`
exact, so injectivity of `J⁰` and `J¹` produces a *partial* retraction
`(retractionZero, retractionOne)` of the comparison `φ : J ⟶ P I` in degrees zero and one — it
cannot be extended further, since `P I` is not exact in positive degrees.  Injectivity of `J⁰` and
`J¹` again then produces `homotopyZero` and `homotopyOne` exhibiting `φ ∘ retraction` as the
identity up to homotopy in degree one.  That identity is exactly what
`HomologicalComplex.mono_homologyMap_iff_up_to_refinements` asks for, and no refinement is even
needed: the witness is built from the retraction and the homotopy on the nose.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {ι : Type w} {c : ComplexShape ι}
  {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]

omit [Abelian D] in
/-- Bracket shuffling: a three-fold composite that is known to factor through `e` still does so
after a fourth morphism.  Stated over *variable* objects, because at the concrete objects of
interest the junction between `(HomologicalComplex.homologyFunctor D c n).obj K` and `K.homology n`
is only a definitional equality, and `Category.assoc` cannot be applied by `rw` across it. -/
theorem comp_comp_comp_eq {W X Y Z T : D} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ T)
    (e : W ⟶ Z) (h : a ≫ b ≫ c = e) : a ≫ b ≫ c ≫ d = e ≫ d := by
  rw [← h]
  simp only [Category.assoc]

/-- Bracket shuffling for the vanishing of a four-fold composite: if the last two factors
regroup as `u ≫ v` and the second factor kills `u`, the composite is zero.  Stated over
*variable* objects for the same reason as `comp_comp_comp_eq`. -/
theorem comp_eq_zero_of_mid {V W X Y Z T : D} (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y) (g : Y ⟶ Z)
    (u : X ⟶ T) (v : T ⟶ Z) (hcg : c ≫ g = u ≫ v) (hbu : b ≫ u = 0) :
    (a ≫ b ≫ c) ≫ g = 0 := by
  rw [Category.assoc, Category.assoc, hcg, ← Category.assoc b u v, hbu, zero_comp, comp_zero]

section Cycles

variable (Q : B ⥤ D) [Q.Additive]

/-- The canonical comparison `Q (Zⁱ C) ⟶ Zⁱ (Q C)` between `Q` applied to the cycles of a
homological complex and the cycles of `Q` applied to that complex: the cycle of `Q C` determined
by `Q` applied to the inclusion of the cycles of `C`. -/
def mapCycles (C : HomologicalComplex B c) (i : ι) :
    Q.obj (C.cycles i) ⟶
      ((Q.mapHomologicalComplex c).obj C).cycles i :=
  HomologicalComplex.liftCycles _ (Q.map (C.iCycles i)) (c.next i) rfl (by
    change Q.map (C.iCycles i) ≫ Q.map (C.d i (c.next i)) = 0
    rw [← Q.map_comp, C.iCycles_d, Q.map_zero])

/-- The defining property of `mapCycles`: followed by the inclusion of the cycles of `Q C`, it is
`Q` applied to the inclusion of the cycles of `C`. -/
@[reassoc (attr := simp)]
lemma mapCycles_i (C : HomologicalComplex B c) (i : ι) :
    mapCycles Q C i ≫ ((Q.mapHomologicalComplex c).obj C).iCycles i =
      Q.map (C.iCycles i) :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The comparison of cycles is natural in the complex. -/
@[reassoc]
lemma mapCycles_naturality {C C' : HomologicalComplex B c} (ψ : C ⟶ C') (i : ι) :
    Q.map (HomologicalComplex.cyclesMap ψ i) ≫ mapCycles Q C' i =
      mapCycles Q C i ≫ HomologicalComplex.cyclesMap
        ((Q.mapHomologicalComplex c).map ψ) i := by
  rw [← cancel_mono (((Q.mapHomologicalComplex c).obj C').iCycles i),
    Category.assoc, Category.assoc, mapCycles_i, HomologicalComplex.cyclesMap_i,
    mapCycles_i_assoc, ← Q.map_comp, HomologicalComplex.cyclesMap_i, Q.map_comp]
  rfl

/-- **A left exact functor preserves cycles.**  Both `Q (Zⁱ C)` and `Zⁱ (Q C)` are kernels of
`Q` applied to the differential out of degree `i`, and the comparison `mapCycles` is the induced
map between them. -/
instance isIso_mapCycles [PreservesFiniteLimits Q] (C : HomologicalComplex B c) (i : ι) :
    IsIso (mapCycles Q C i) := by
  have h₁ : IsLimit ((KernelFork.ofι (C.iCycles i) (C.iCycles_d i (c.next i))).map Q) :=
    KernelFork.mapIsLimit _ (C.cyclesIsKernel i (c.next i) rfl) Q
  have hw : ((Q.mapHomologicalComplex c).obj C).iCycles i ≫
      Q.map (C.d i (c.next i)) = 0 :=
    ((Q.mapHomologicalComplex c).obj C).iCycles_d i (c.next i)
  have hlift : h₁.lift (KernelFork.ofι _ hw) ≫ Q.map (C.iCycles i) =
      ((Q.mapHomologicalComplex c).obj C).iCycles i :=
    Fork.IsLimit.lift_ι h₁
  refine ⟨h₁.lift (KernelFork.ofι _ hw), Fork.IsLimit.hom_ext h₁ ?_, ?_⟩
  · change (mapCycles Q C i ≫ _) ≫ Q.map (C.iCycles i) = 𝟙 _ ≫ Q.map (C.iCycles i)
    rw [Category.assoc, hlift, mapCycles_i, Category.id_comp]
  · rw [← cancel_mono (((Q.mapHomologicalComplex c).obj C).iCycles i),
      Category.assoc, mapCycles_i, hlift, Category.id_comp]

/-- The comparison of cycles of a left exact functor, as an isomorphism. -/
def mapCyclesIso [PreservesFiniteLimits Q] (C : HomologicalComplex B c) (i : ι) :
    Q.obj (C.cycles i) ≅
      ((Q.mapHomologicalComplex c).obj C).cycles i :=
  asIso (mapCycles Q C i)

/-- The forward map of `mapCyclesIso` is the comparison `mapCycles`. -/
@[simp]
lemma mapCyclesIso_hom [PreservesFiniteLimits Q] (C : HomologicalComplex B c) (i : ι) :
    (mapCyclesIso Q C i).hom = mapCycles Q C i :=
  rfl

/-- The inverse comparison of cycles is natural in the complex. -/
@[reassoc]
lemma mapCyclesIso_inv_naturality [PreservesFiniteLimits Q] {C C' : HomologicalComplex B c}
    (ψ : C ⟶ C') (i : ι) :
    HomologicalComplex.cyclesMap ((Q.mapHomologicalComplex c).map ψ) i ≫
        (mapCyclesIso Q C' i).inv =
      (mapCyclesIso Q C i).inv ≫ Q.map (HomologicalComplex.cyclesMap ψ i) := by
  rw [← cancel_mono (mapCyclesIso Q C' i).hom, Category.assoc,
    (mapCyclesIso Q C' i).inv_hom_id, Category.comp_id, Category.assoc,
    mapCyclesIso_hom Q C' i, mapCycles_naturality, ← mapCyclesIso_hom Q C i,
    ← Category.assoc, (mapCyclesIso Q C i).inv_hom_id, Category.id_comp]

/-- The boundaries of `Q C` are `Q` applied to the boundaries of `C`, through the comparison of
cycles. -/
@[reassoc]
lemma toCycles_comp_mapCyclesIso_inv [PreservesFiniteLimits Q] (C : HomologicalComplex B c)
    (i j : ι) :
    ((Q.mapHomologicalComplex c).obj C).toCycles i j ≫
        (mapCyclesIso Q C j).inv = Q.map (C.toCycles i j) := by
  rw [Iso.comp_inv_eq, mapCyclesIso_hom,
    ← cancel_mono (((Q.mapHomologicalComplex c).obj C).iCycles j),
    Category.assoc, mapCycles_i, HomologicalComplex.toCycles_i, ← Q.map_comp,
    HomologicalComplex.toCycles_i]
  rfl

end Cycles

section Homology

variable (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q]

/-- **The comparison `Hⁱ (Q C) ⟶ Q (Hⁱ C)` for a left exact functor `Q`.**  The homology of
`Q C` is the cokernel of the boundaries inside its cycles, and `Q` applied to the projection onto
`Hⁱ C`, read through the isomorphism `mapCyclesIso`, kills those boundaries. -/
def homologyToMapHomology (C : HomologicalComplex B c) (i : ι) :
    ((Q.mapHomologicalComplex c).obj C).homology i ⟶ Q.obj (C.homology i) :=
  (((Q.mapHomologicalComplex c).obj C).homologyIsCokernel (c.prev i) i rfl).desc
    (CokernelCofork.ofπ ((mapCyclesIso Q C i).inv ≫ Q.map (C.homologyπ i)) (by
      rw [toCycles_comp_mapCyclesIso_inv_assoc, ← Q.map_comp,
        HomologicalComplex.toCycles_comp_homologyπ, Q.map_zero]))

/-- The defining property of `homologyToMapHomology`: on cycles it is `Q` applied to the
projection onto homology. -/
@[reassoc]
lemma homologyπ_comp_homologyToMapHomology (C : HomologicalComplex B c) (i : ι) :
    ((Q.mapHomologicalComplex c).obj C).homologyπ i ≫
        homologyToMapHomology Q C i =
      (mapCyclesIso Q C i).inv ≫ Q.map (C.homologyπ i) :=
  Cofork.IsColimit.π_desc
    (((Q.mapHomologicalComplex c).obj C).homologyIsCokernel (c.prev i) i rfl)

/-- The defining property of `homologyToMapHomology`, with the comparison of cycles cancelled:
`Q` applied to the projection onto homology factors through `homologyToMapHomology`. -/
@[reassoc]
lemma mapCycles_comp_homologyπ_comp_homologyToMapHomology (C : HomologicalComplex B c) (i : ι) :
    mapCycles Q C i ≫ ((Q.mapHomologicalComplex c).obj C).homologyπ i ≫
        homologyToMapHomology Q C i = Q.map (C.homologyπ i) := by
  rw [homologyπ_comp_homologyToMapHomology, ← mapCyclesIso_hom, Iso.hom_inv_id_assoc]

/-- The comparison `Hⁱ (Q C) ⟶ Q (Hⁱ C)` is natural in the complex. -/
@[reassoc]
lemma homologyToMapHomology_naturality {C C' : HomologicalComplex B c} (ψ : C ⟶ C') (i : ι) :
    HomologicalComplex.homologyMap ((Q.mapHomologicalComplex c).map ψ) i ≫
        homologyToMapHomology Q C' i =
      homologyToMapHomology Q C i ≫ Q.map (HomologicalComplex.homologyMap ψ i) := by
  rw [← cancel_epi (((Q.mapHomologicalComplex c).obj C).homologyπ i),
    HomologicalComplex.homologyπ_naturality_assoc, homologyπ_comp_homologyToMapHomology,
    homologyπ_comp_homologyToMapHomology_assoc, mapCyclesIso_inv_naturality_assoc,
    ← Q.map_comp, ← Q.map_comp, HomologicalComplex.homologyπ_naturality]

/-- **An exact functor commutes with homology.**  When `Q` preserves finite colimits as well as
finite limits, the comparison `Hⁱ (Q C) ⟶ Q (Hⁱ C)` is an isomorphism: both sides are cokernels
of the boundary inclusion, `Q` applied to the cycles being the cycles of `Q C`. -/
instance isIso_homologyToMapHomology [PreservesFiniteColimits Q] (C : HomologicalComplex B c)
    (i : ι) : IsIso (homologyToMapHomology Q C i) := by
  have hc : IsColimit ((CokernelCofork.ofπ (C.homologyπ i)
      (C.toCycles_comp_homologyπ (c.prev i) i)).map Q) :=
    CokernelCofork.mapIsColimit _ (C.homologyIsCokernel (c.prev i) i rfl) Q
  have hzero : Q.map (C.toCycles (c.prev i) i) ≫
      mapCycles Q C i ≫ ((Q.mapHomologicalComplex c).obj C).homologyπ i = 0 := by
    rw [← toCycles_comp_mapCyclesIso_inv (Q := Q) (C := C) (i := c.prev i) (j := i),
      Category.assoc, ← mapCyclesIso_hom Q C i, Iso.inv_hom_id_assoc,
      HomologicalComplex.toCycles_comp_homologyπ]
  have hπ : Q.map (C.homologyπ i) ≫ hc.desc (CokernelCofork.ofπ _ hzero) =
      mapCycles Q C i ≫ ((Q.mapHomologicalComplex c).obj C).homologyπ i :=
    Cofork.IsColimit.π_desc hc
  have hepi : Epi (Q.map (C.homologyπ i)) := epi_of_isColimit_cofork hc
  refine ⟨hc.desc (CokernelCofork.ofπ _ hzero), ?_, ?_⟩
  · rw [← cancel_epi (((Q.mapHomologicalComplex c).obj C).homologyπ i),
      homologyπ_comp_homologyToMapHomology_assoc, Category.comp_id, hπ,
      ← mapCyclesIso_hom Q C i, Iso.inv_hom_id_assoc]
  · rw [← cancel_epi (Q.map (C.homologyπ i)), Category.comp_id, ← Category.assoc, hπ,
      Category.assoc, mapCycles_comp_homologyπ_comp_homologyToMapHomology]

/-- `homologyToMapHomology` with its source spelled as the value of the homology *functor*.  This
is the same morphism, retyped: the two spellings of the source are definitionally equal, but only
this one can be composed with `Stacks.Cohomology.RightDerivedEdge.isoRightDerivedObjComp` by the
rewriting tactics. -/
def homologyFunctorToMapHomology (C : HomologicalComplex B c) (i : ι) :
    (HomologicalComplex.homologyFunctor D c i).obj
        ((Q.mapHomologicalComplex c).obj C) ⟶ Q.obj (C.homology i) :=
  homologyToMapHomology Q C i

/-- `homologyToMapHomology_naturality` in the spelling of `homologyFunctorToMapHomology`. -/
@[reassoc]
lemma homologyFunctorToMapHomology_naturality {C C' : HomologicalComplex B c} (ψ : C ⟶ C')
    (i : ι) :
    (HomologicalComplex.homologyFunctor D c i).map
          ((Q.mapHomologicalComplex c).map ψ) ≫
        homologyFunctorToMapHomology Q C' i =
      homologyFunctorToMapHomology Q C i ≫ Q.map (HomologicalComplex.homologyMap ψ i) :=
  homologyToMapHomology_naturality Q ψ i

/-- The defining property of `homologyToMapHomology` in the spelling of
`homologyFunctorToMapHomology`. -/
@[reassoc]
lemma mapCycles_comp_homologyπ_comp_homologyFunctorToMapHomology (C : HomologicalComplex B c)
    (i : ι) :
    mapCycles Q C i ≫ ((Q.mapHomologicalComplex c).obj C).homologyπ i ≫
        homologyFunctorToMapHomology Q C i = Q.map (C.homologyπ i) :=
  mapCycles_comp_homologyπ_comp_homologyToMapHomology Q C i

/-- An injective resolution has no higher homology. -/
theorem isZero_homology_succ {Z : B} (K : InjectiveResolution Z) (n : ℕ) :
    IsZero (K.cocomplex.homology (n + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).2
    (K.exact_succ n)

/-- **A morphism out of an injective resolution dies under the comparison
`Hⁿ⁺¹(Q C) ⟶ Q (Hⁿ⁺¹ C)`**: by naturality it factors through `Q` applied to `Hⁿ⁺¹` of the
resolution, which vanishes.  This is the degreewise reason the two edge morphisms compose to
zero. -/
theorem homologyMap_comp_homologyFunctorToMapHomology_eq_zero {Z : B}
    (K : InjectiveResolution Z) {C : CochainComplex B ℕ} (ψ : K.cocomplex ⟶ C) (n : ℕ) :
    HomologicalComplex.homologyMap
          ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) (n + 1) ≫
        homologyFunctorToMapHomology Q C (n + 1) = 0 := by
  rw [homologyFunctorToMapHomology, homologyToMapHomology_naturality,
    (isZero_homology_succ K n).eq_of_src (HomologicalComplex.homologyMap ψ (n + 1)) 0,
    Q.map_zero, comp_zero]

end Homology

/-- The first edge morphism, computed on the globally chosen injective resolutions. -/
private theorem edge_app_eq_chosen [HasInjectiveResolutions A] [HasInjectiveResolutions B]
    (P : A ⥤ B) [P.Additive] [P.PreservesInjectiveObjects] (Q : B ⥤ D) [Q.Additive] (n : ℕ)
    (Z : A) :
    (RightDerivedEdge.edge P Q n).app Z =
      ((injectiveResolution (P.obj Z)).isoRightDerivedObj Q n).hom ≫
        HomologicalComplex.homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (RightDerivedEdge.resolutionComparison P Z)) n ≫
        ((injectiveResolution Z).isoRightDerivedObj (P ⋙ Q) n).inv :=
  RightDerivedEdge.edge_app_eq P Q n _ _ _ (RightDerivedEdge.ι_f_zero_comp_resolutionComparison P Z)

section CoEdge

variable [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  (P : A ⥤ B) [P.Additive] [P.PreservesInjectiveObjects]
  (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q]

/-- The component of the co-edge morphism at an object, computed on the globally chosen injective
resolution.  This is bundled into a natural transformation by `secondEdge`. -/
def secondEdgeApp (n : ℕ) (X : A) :
    ((P ⋙ Q).rightDerived n).obj X ⟶ Q.obj ((P.rightDerived n).obj X) :=
  (RightDerivedEdge.isoRightDerivedObjComp P Q (injectiveResolution X) n).hom ≫
    homologyFunctorToMapHomology Q
      ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex) n ≫
    Q.map ((injectiveResolution X).isoRightDerivedObj P n).inv

omit [HasInjectiveResolutions B] [P.PreservesInjectiveObjects] in
/-- **Any injective resolution computes the component of the co-edge morphism.**  The comparison
between two resolutions is used on both ends simultaneously, so no homotopy uniqueness statement
is needed. -/
@[reassoc]
theorem isoRightDerivedObjComp_inv_comp_secondEdgeApp (n : ℕ) {X : A}
    (I : InjectiveResolution X) :
    (RightDerivedEdge.isoRightDerivedObjComp P Q I n).inv ≫ secondEdgeApp P Q n X =
      homologyFunctorToMapHomology Q
          ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) n ≫
        Q.map (I.isoRightDerivedObj P n).inv := by
  have hcomm : I.ι.f 0 ≫
      (InjectiveResolution.desc (𝟙 X) (injectiveResolution X) I).f 0 =
        𝟙 X ≫ (injectiveResolution X).ι.f 0 :=
    InjectiveResolution.desc_commutes_zero _ _ _
  have hQ := RightDerivedEdge.isoRightDerivedObjComp_inv_naturality P Q (𝟙 X) I
    (injectiveResolution X) (InjectiveResolution.desc (𝟙 X) (injectiveResolution X) I) hcomm n
  have hP0 := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 X) I
    (injectiveResolution X) (InjectiveResolution.desc (𝟙 X) (injectiveResolution X) I) hcomm P n
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hQ hP0
  have hP : (I.isoRightDerivedObj P n).inv =
      HomologicalComplex.homologyMap ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc (𝟙 X) (injectiveResolution X) I)) n ≫
        ((injectiveResolution X).isoRightDerivedObj P n).inv := hP0
  rw [hQ, secondEdgeApp, Category.assoc, Iso.inv_hom_id_assoc,
    homologyFunctorToMapHomology_naturality_assoc]
  exact congrArg _ (RightDerivedEdge.map_comp_eq_map Q _ _ _ hP.symm)

/-- **The co-edge morphism of a composite of right derived functors.**  For additive functors
`P : A ⥤ B` and `Q : B ⥤ D` with `P` preserving injective objects and `Q` left exact, this is the
natural transformation `Rⁿ (Q ∘ P) ⟶ Q ∘ Rⁿ P`.  It is the edge morphism
`H^n ⟶ E₂^{0,n}` of the Grothendieck spectral sequence of `(P, Q)`. -/
def secondEdge (n : ℕ) : (P ⋙ Q).rightDerived n ⟶ P.rightDerived n ⋙ Q where
  app X := secondEdgeApp P Q n X
  naturality X Y g := by
    have hcomm : (injectiveResolution X).ι.f 0 ≫
        (InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X)).f 0 =
          g ≫ (injectiveResolution Y).ι.f 0 :=
      InjectiveResolution.desc_commutes_zero _ _ _
    have hQ := RightDerivedEdge.isoRightDerivedObjComp_inv_naturality P Q g
      (injectiveResolution X) (injectiveResolution Y)
      (InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X)) hcomm n
    have hP := InjectiveResolution.isoRightDerivedObj_inv_naturality g (injectiveResolution X)
      (injectiveResolution Y)
      (InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X)) hcomm P n
    have hP' : ((injectiveResolution X).isoRightDerivedObj P n).inv ≫
        (P.rightDerived n).map g =
          HomologicalComplex.homologyMap ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map
              (InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X))) n ≫
            ((injectiveResolution Y).isoRightDerivedObj P n).inv := hP
    rw [← cancel_epi
      (RightDerivedEdge.isoRightDerivedObjComp P Q (injectiveResolution X) n).inv]
    dsimp only [Functor.comp_map]
    rw [← Category.assoc, hQ, Category.assoc,
      isoRightDerivedObjComp_inv_comp_secondEdgeApp P Q n (injectiveResolution Y),
      isoRightDerivedObjComp_inv_comp_secondEdgeApp_assoc P Q n (injectiveResolution X),
      homologyFunctorToMapHomology_naturality_assoc]
    exact congrArg _ (RightDerivedEdge.map_comp_eq_map_comp Q _ _ _ _ hP'.symm)

omit [HasInjectiveResolutions B] [P.PreservesInjectiveObjects] in
/-- **Any injective resolution computes the co-edge morphism**, in the form consumers use: the
projection onto homology of `Q` applied to `P` applied to the resolution, read through the two
comparison isomorphisms, is `Q` applied to the projection onto the higher derived functor. -/
theorem secondEdge_app_eq (n : ℕ) {X : A} (I : InjectiveResolution X) :
    mapCycles Q ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) n ≫
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).homologyπ n ≫
        (I.isoRightDerivedObj (P ⋙ Q) n).inv ≫ (secondEdge P Q n).app X =
      Q.map (((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ n) ≫
        Q.map (I.isoRightDerivedObj P n).inv := by
  have h := mapCycles_comp_homologyπ_comp_homologyFunctorToMapHomology Q
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) n
  change mapCycles Q _ n ≫ _ ≫ (RightDerivedEdge.isoRightDerivedObjComp P Q I n).inv ≫
    secondEdgeApp P Q n X = _
  rw [isoRightDerivedObjComp_inv_comp_secondEdgeApp P Q n I]
  exact comp_comp_comp_eq _ _ _ _ _ h

/-- **The two edge morphisms compose to zero in every positive degree.**  Both are characterised
at the same injective resolution `I` of `X`, so the composite is `Q` applied to the map
`Hⁿ⁺¹(J) ⟶ Hⁿ⁺¹(P I)` induced by the comparison `J ⟶ P I`, and `Hⁿ⁺¹(J)` vanishes because `J` is a
resolution. -/
theorem edge_comp_secondEdge (n : ℕ) (Z : A) :
    (RightDerivedEdge.edge P Q (n + 1)).app Z ≫ (secondEdge P Q (n + 1)).app Z = 0 := by
  rw [edge_app_eq_chosen]
  exact comp_eq_zero_of_mid _ _ _ _ _ _
    (isoRightDerivedObjComp_inv_comp_secondEdgeApp P Q (n + 1) (injectiveResolution Z))
    (homologyMap_comp_homologyFunctorToMapHomology_eq_zero Q (injectiveResolution (P.obj Z))
      (RightDerivedEdge.resolutionComparison P Z) n)

end CoEdge

section EdgeMono

omit [Abelian B] [Abelian D] in
/-- A monomorphism between two isomorphisms is a monomorphism. -/
theorem mono_sandwich {W X' Y' Z' : D} (a : W ≅ X') (b : X' ⟶ Y') (c : Z' ≅ Y')
    (hb : Mono b) : Mono (a.hom ≫ b ≫ c.inv) := by
  have := hb
  infer_instance

variable [HasInjectiveResolutions A] (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P]
  {X : A} (I : InjectiveResolution X) (J : InjectiveResolution (P.obj X))

omit [HasInjectiveResolutions A] [PreservesFiniteLimits P] in
/-- The augmentation of an injective resolution, out of the resolved object rather than out of the
degree-zero term of the single complex.  The two sources are only definitionally equal, and naming
the morphism at the object is what lets `P` applied to one augmentation be composed with
another. -/
def augOf {Z : B} (K : InjectiveResolution Z) : Z ⟶ K.cocomplex.X 0 := K.ι.f 0

omit [HasInjectiveResolutions A] [PreservesFiniteLimits P] in
/-- The augmentation is killed by the first differential. -/
@[reassoc]
theorem augOf_comp_d {Z : B} (K : InjectiveResolution Z) :
    augOf K ≫ K.cocomplex.d 0 1 = 0 :=
  K.ι_f_zero_comp_complex_d

omit [HasInjectiveResolutions A] [PreservesFiniteLimits P] in
/-- `CategoryTheory.InjectiveResolution.exact₀` in the spelling of `augOf`. -/
theorem exact_augOf {Z : B} (K : InjectiveResolution Z) :
    (ShortComplex.mk (augOf K) (K.cocomplex.d 0 1) (augOf_comp_d K)).Exact :=
  K.exact₀

/-- `P` applied to the augmentation of an injective resolution, out of `P X`. -/
def mapAug : P.obj X ⟶ ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).X 0 :=
  P.map (I.ι.f 0)

omit [HasInjectiveResolutions A] [PreservesFiniteLimits P] in
/-- `P` applied to the augmentation is killed by the first differential. -/
@[reassoc]
theorem mapAug_comp_d :
    mapAug P I ≫ ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).d 0 1 = 0 :=
  RightDerivedEdge.map_ι_f_zero_comp_d P I

/-- The augmentation of `P` applied to an injective resolution is a monomorphism, because a left
exact `P` preserves the kernel fork exhibiting `X` inside `I⁰`. -/
instance mono_mapAug : Mono (mapAug P I) :=
  mono_of_isLimit_fork (KernelFork.mapIsLimit _ I.isLimitKernelFork P)

omit [HasInjectiveResolutions A] in
/-- **`P` applied to an injective resolution stays exact in degree zero** when `P` is left exact:
`0 ⟶ P X ⟶ (P I)⁰ ⟶ (P I)¹` is exact.  This is the only place left exactness of `P` enters; in
positive degrees `P I` is of course no longer exact, and that failure is what the spectral
sequence measures. -/
theorem exact_mapAug :
    (ShortComplex.mk (mapAug P I)
        (((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).d 0 1)
        (mapAug_comp_d P I)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ I.isLimitKernelFork P)

/-- The degree-zero component of the partial retraction of a comparison `J ⟶ P I`: `J⁰` is
injective and `P X ⟶ (P I)⁰` is a monomorphism, so the augmentation of `J` extends over it. -/
def retractionZero :
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).X 0 ⟶ J.cocomplex.X 0 :=
  Injective.factorThru (augOf J) (mapAug P I)

omit [HasInjectiveResolutions A] in
/-- The degree-zero retraction extends the augmentation. -/
@[reassoc]
theorem mapAug_comp_retractionZero : mapAug P I ≫ retractionZero P I J = augOf J :=
  Injective.comp_factorThru _ _

omit [HasInjectiveResolutions A] in
/-- The side condition defining `retractionOne`. -/
theorem mapAug_comp_retractionZero_comp_d :
    mapAug P I ≫ retractionZero P I J ≫ J.cocomplex.d 0 1 = 0 := by
  rw [mapAug_comp_retractionZero_assoc, augOf_comp_d]

/-- The degree-one component of the partial retraction: `retractionZero` followed by the
differential of `J` kills `P X`, so by exactness of `0 ⟶ P X ⟶ (P I)⁰ ⟶ (P I)¹` and injectivity
of `J¹` it factors through `(P I)¹`.  It cannot be pushed to degree two, since `P I` is not exact
there — which is why only the first edge map is handled this way. -/
def retractionOne :
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).X 1 ⟶ J.cocomplex.X 1 :=
  (exact_mapAug P I).descToInjective (retractionZero P I J ≫ J.cocomplex.d 0 1)
    (mapAug_comp_retractionZero_comp_d P I J)

omit [HasInjectiveResolutions A] in
/-- The partial retraction is a morphism of complexes in degrees zero and one. -/
@[reassoc]
theorem d_comp_retractionOne :
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).d 0 1 ≫
        retractionOne P I J = retractionZero P I J ≫ J.cocomplex.d 0 1 :=
  (exact_mapAug P I).comp_descToInjective _ _

variable (φ : J.cocomplex ⟶ (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  (hφ : augOf J ≫ φ.f 0 = mapAug P I)

omit [HasInjectiveResolutions A] in
include hφ in
/-- The side condition defining `homotopyZero`. -/
theorem augOf_comp_comparison_comp_retractionZero_sub :
    augOf J ≫ (φ.f 0 ≫ retractionZero P I J - 𝟙 _) = 0 := by
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hφ,
    mapAug_comp_retractionZero, sub_self]

/-- The degree-zero component of the homotopy from `φ ∘ retraction` to the identity: the
difference `φ⁰ ∘ retractionZero - 𝟙` vanishes on the augmentation of `J`, so by exactness of
`0 ⟶ P X ⟶ J⁰ ⟶ J¹` and injectivity of `J⁰` it factors through `J¹`. -/
def homotopyZero : J.cocomplex.X 1 ⟶ J.cocomplex.X 0 :=
  (exact_augOf J).descToInjective (φ.f 0 ≫ retractionZero P I J - 𝟙 _)
    (augOf_comp_comparison_comp_retractionZero_sub P I J φ hφ)

omit [HasInjectiveResolutions A] in
/-- The defining property of `homotopyZero`. -/
@[reassoc]
theorem d_comp_homotopyZero :
    J.cocomplex.d 0 1 ≫ homotopyZero P I J φ hφ = φ.f 0 ≫ retractionZero P I J - 𝟙 _ :=
  (exact_augOf J).comp_descToInjective _ _

omit [HasInjectiveResolutions A] in
/-- The side condition defining `homotopyOne`. -/
theorem d_comp_comparison_comp_retractionOne_sub :
    J.cocomplex.d 0 1 ≫ (φ.f 1 ≫ retractionOne P I J - 𝟙 _ -
        homotopyZero P I J φ hφ ≫ J.cocomplex.d 0 1) = 0 := by
  simp only [Preadditive.comp_sub, Category.comp_id, Category.assoc,
    ← HomologicalComplex.Hom.comm_assoc, d_comp_retractionOne, d_comp_homotopyZero_assoc,
    Preadditive.sub_comp, Category.id_comp]
  abel

/-- The degree-one component of the homotopy from `φ ∘ retraction` to the identity. -/
def homotopyOne : J.cocomplex.X 2 ⟶ J.cocomplex.X 1 :=
  (J.exact_succ 0).descToInjective
    (φ.f 1 ≫ retractionOne P I J - 𝟙 _ - homotopyZero P I J φ hφ ≫ J.cocomplex.d 0 1)
    (d_comp_comparison_comp_retractionOne_sub P I J φ hφ)

omit [HasInjectiveResolutions A] in
/-- The defining property of `homotopyOne`. -/
@[reassoc]
theorem d_comp_homotopyOne :
    J.cocomplex.d 1 2 ≫ homotopyOne P I J φ hφ =
      φ.f 1 ≫ retractionOne P I J - 𝟙 _ -
        homotopyZero P I J φ hφ ≫ J.cocomplex.d 0 1 :=
  (J.exact_succ 0).comp_descToInjective _ _

omit [HasInjectiveResolutions A] in
/-- **In degree one the comparison of resolutions is split by the partial retraction, up to
homotopy.**  This identity between endomorphisms of `J¹` is the whole content of the injectivity
of the edge morphism, and an additive `Q` carries it over verbatim. -/
theorem comparison_comp_retractionOne :
    φ.f 1 ≫ retractionOne P I J =
      𝟙 _ + J.cocomplex.d 1 2 ≫ homotopyOne P I J φ hφ +
        homotopyZero P I J φ hφ ≫ J.cocomplex.d 0 1 := by
  rw [d_comp_homotopyOne]
  abel

omit [HasInjectiveResolutions A] in
include hφ in
/-- **The map induced on first homology by the comparison of resolutions is a monomorphism.**  By
`HomologicalComplex.mono_homologyMap_iff_up_to_refinements` it suffices, for a cycle
`x₂ : T ⟶ Q J¹` whose image in `Q (P I)¹` is the boundary of some `y₁ : T ⟶ Q (P I)⁰`, to exhibit
`x₂` as a boundary after an epimorphism; the partial retraction and the homotopy give the witness
outright, so the epimorphism may be taken to be the identity. -/
theorem mono_homologyMap_map_one (Q : B ⥤ D) [Q.Additive] :
    Mono (HomologicalComplex.homologyMap
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) 1) := by
  rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ 0 1 2 (by simp) (by simp)]
  intro T x₂ hx₂ y₁ hy₁
  refine ⟨T, 𝟙 T, inferInstance,
    y₁ ≫ Q.map (retractionZero P I J) - x₂ ≫ Q.map (homotopyZero P I J φ hφ), ?_⟩
  have hx : x₂ ≫ Q.map (J.cocomplex.d 1 2) = 0 := hx₂
  have hy : x₂ ≫ Q.map (φ.f 1) =
      y₁ ≫ Q.map (((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).d 0 1) := hy₁
  have hd : ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).d 0 1 =
      Q.map (J.cocomplex.d 0 1) := rfl
  rw [Category.id_comp, hd, Preadditive.sub_comp, Category.assoc, Category.assoc,
    ← Q.map_comp (retractionZero P I J) (J.cocomplex.d 0 1),
    ← Q.map_comp (homotopyZero P I J φ hφ) (J.cocomplex.d 0 1),
    ← d_comp_retractionOne P I J,
    Q.map_comp (((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).d 0 1)
      (retractionOne P I J),
    ← Category.assoc y₁, ← hy, Category.assoc,
    ← Q.map_comp (φ.f 1) (retractionOne P I J), comparison_comp_retractionOne P I J φ hφ,
    Q.map_add, Q.map_add, Q.map_id, Preadditive.comp_add, Preadditive.comp_add]
  have hvanish : x₂ ≫ Q.map (J.cocomplex.d 1 2 ≫ homotopyOne P I J φ hφ) = 0 := by
    rw [Q.map_comp, ← Category.assoc, hx, zero_comp]
  have hid : x₂ ≫ 𝟙 (Q.obj (J.cocomplex.X 1)) = x₂ := Category.comp_id x₂
  rw [hvanish, hid]
  abel

/-- **The first edge morphism is a monomorphism in degree one** when `P` is left exact: for
`P = f_*` and `Q = Γ(Y, -)` this is the injectivity of `H¹(Y, f_* F) ⟶ H¹(X, F)`. -/
theorem mono_edge_app_one [HasInjectiveResolutions B] [P.PreservesInjectiveObjects]
    (Q : B ⥤ D) [Q.Additive] (Z : A) :
    Mono ((RightDerivedEdge.edge P Q 1).app Z) := by
  rw [edge_app_eq_chosen]
  exact mono_sandwich ((injectiveResolution (P.obj Z)).isoRightDerivedObj Q 1) _
    ((injectiveResolution Z).isoRightDerivedObj (P ⋙ Q) 1)
    (mono_homologyMap_map_one P (injectiveResolution Z) (injectiveResolution (P.obj Z))
      (RightDerivedEdge.resolutionComparison P Z)
      (RightDerivedEdge.ι_f_zero_comp_resolutionComparison P Z) Q)

end EdgeMono

end Stacks.Cohomology.RightDerivedCoEdge

end
