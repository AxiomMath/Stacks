module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import Mathlib.CategoryTheory.Sites.Coverage
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Limits
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Comparing the small and the big crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`.  The small crystalline site `Cris(X/S)` is
the full subcategory of the big one `CRIS(X/S)` on the divided power thickenings `(U, T, δ)` whose
map `U ⟶ X` is an open immersion, with the Zariski topology it inherits.  The inclusion functor
`Cris(X/S) ⥤ CRIS(X/S)` commutes with the finite limits that exist in `CRIS(X/S)`, is fully
faithful, and is both continuous and cocontinuous; so it induces a morphism of topoi
`i : (X/S)_cris ⟶ (X/S)_CRIS` whose inverse image is plain restriction of a sheaf on the big site
to the small one, and that restriction has a left adjoint `i_!` of which it is a retraction.

Closure of the small category under finite limits is a statement about open immersions into `X`:
the forgetful functor `CRIS(X/S) ⥤ Sch/X` preserves limits, and a finite limit of opens of `X` in
`Sch/X` is again an open of `X`, the terminal object being `X` itself and a fibre product being an
intersection.

Both site-functor properties are checked on the Zariski covering families, which generate the two
topologies.  Cocontinuity is the restriction of an object of `Cris(X/S)` to the opens of its
ambient scheme over which a given morphism factors through the members of a covering family, as
for change of divided power base.  Continuity is the sheaf condition for such a family, and what
it needs is that a family of sections compatible over the vertices lying in `Cris(X/S)` is
compatible over all vertices in `CRIS(X/S)`: a commuting square over an object of `Cris(X/S)`
whose two legs are members of a Zariski covering family is dominated by one whose vertex is the
restriction of one member to the open over which it factors through the other, and that vertex
lies in `Cris(X/S)`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.liftHomOfTop` — the factorization of a
  morphism of `CRIS(X/S)` through a Cartesian open immersion whose ambient image covers it.
* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.smallCoverage` — the Zariski
  covering families of `Cris(X/S)` as a coverage, which is what lets the sheaf condition be
  checked on them.
* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.smallToBigMorphism` — the morphism
  of topoi `i : (X/S)_cris ⟶ (X/S)_CRIS`, [Stacks, Tag 07IJ].
* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.ιSheafAdjunctionLowerShriek` — the
  lower shriek `i_!` along the inclusion, left adjoint to restriction.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.isClosedUnderFiniteLimits_isCrystalline` and
  `Crystalline.GlobalCrystallineSituation.CrystallineThickening.ιCreatesLimit` — the inclusion
  creates, hence commutes with, the finite limits that exist in `CRIS(X/S)`.  This is the first
  assertion of [Stacks, Tag 07IJ] shape by shape; see the implementation notes for where the
  assertion itself, which assumes no limits anywhere, is stated and registered.
* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.ι_isCocontinuous` and
  `Crystalline.GlobalCrystallineSituation.CrystallineThickening.ι_isContinuous` — the inclusion is
  cocontinuous and continuous, [Stacks, Tag 07IJ].
* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.inverseImageIsoRestriction`
  — the inverse image `i^{-1}` is restriction, which is the direct image `π_*` of the retraction:
  the formula `π_* = i^{-1}`, [Stacks, Tag 07IJ].
* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.lowerShriekRestrictionIsoId` — the
  composite of the inclusion morphism with the retraction is the identity, on inverse images,
  [Stacks, Tag 07IJ].

## Implementation notes

The existence of nonempty finite limits in `CRIS(X/S)`, clause (1) of [Stacks, Tag 07I9], is
`Crystalline.GlobalCrystallineSituation.hasNonemptyFiniteLimits_thickening` of
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductInstance.lean`.  That module is
not imported here, although it could be without circularity: its closure runs through the affine
layer of the glued binary product and so contains most of the small crystalline tree, which this
file sits beneath.  The existence therefore appears here only as an instance hypothesis
`HasLimitsOfShape J (Thickening S)`, from which instance search, through the closure instance
`Crystalline.GlobalCrystallineSituation.Thickening.isClosedUnderFiniteLimits_isCrystalline` and
Mathlib's instances for full subcategories, gives `HasLimitsOfShape J (CrystallineThickening S)`
and `PreservesLimitsOfShape J (ι S)`; and
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/SmallNonemptyFiniteLimits.lean`, downstream of
both, supplies it and states the first assertion of [Stacks, Tag 07IJ] for every nonempty finite
shape with nothing assumed; that is where the assertion is registered.  For the empty shape the
hypothesis is unsatisfiable in general, `CRIS(X/S)` having no final object, which is why the source
restricts to nonempty shapes.

The retraction `π : (X/S)_CRIS ⟶ (X/S)_cris` is *not* constructed as a morphism of topoi.  Its
inverse image would be `i_!` and its direct image `i^{-1}`, and for that to be a morphism of topoi
`i_!` must be left exact; the source reduces this to exhibiting a set of objects of `Cris(X/S)`
whose representable sheaves cover the final sheaf of `(X/S)_CRIS`, proves it in the affine case
and omits the proof in general.  What is proved here instead is the part of the conclusion that
does not need it: the adjunction `i_! ⊣ i^{-1}`, the identification of `i^{-1}` with restriction,
and that the unit `𝟭 ⟶ i_! ⋙ i^{-1}` is an isomorphism — the inverse image of `π ∘ i = id`.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section OpenImmersionOver

variable (X : Scheme.{u})

private noncomputable instance :
    CreatesFiniteLimits
      (MorphismProperty.overObj (@IsOpenImmersion) (X := X)).ι :=
  createsFiniteLimitsOfCreatesTerminalAndPullbacks _

/-- The opens of a scheme `X`, as a full subcategory of `Sch/X`, are closed under finite limits:
the terminal object is `X` itself and a fibre product of opens over an open is their
intersection. -/
@[ega "I 4.3.1" "special case"]
private instance isClosedUnderFiniteLimits_overObj_isOpenImmersion :
    (MorphismProperty.overObj (@IsOpenImmersion) (X := X)).IsClosedUnderFiniteLimits := by
  refine ⟨fun J _ _ ↦ ?_⟩
  have : HasLimitsOfShape J
      (MorphismProperty.overObj (@IsOpenImmersion) (X := X)).FullSubcategory :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
      (MorphismProperty.overObj (@IsOpenImmersion) (X := X)).ι
  exact ObjectProperty.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι _ _

end OpenImmersionOver

end AlgebraicGeometry

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-! ### Finite limits -/

/-- The small crystalline category is closed under finite limits inside the big one:
a finite limit of divided power thickenings whose maps to `X` are open immersions again has
this property, because the forgetful functor `CRIS(X/S) ⥤ Sch/X` preserves limits and a finite
limit of opens of `X` in `Sch/X` is an open of `X`. -/
instance Thickening.isClosedUnderFiniteLimits_isCrystalline :
    (Thickening.IsCrystalline (S := S)).IsClosedUnderFiniteLimits := by
  refine ⟨fun J _ _ ↦ ?_⟩
  have h : Thickening.IsCrystalline (S := S) =
      (MorphismProperty.overObj (@IsOpenImmersion) (X := S.X)).inverseImage (forget S) := rfl
  rw [h]
  infer_instance

namespace Thickening

/-! ### Factoring a morphism through a Cartesian open immersion -/

section LiftTop

variable {B C D : Thickening S} (q : B ⟶ C) [IsOpenImmersion q.targetHom.hom] (r : D ⟶ C)

/-- If the open of the ambient scheme of `D` over which `r` factors through `q` is everything,
then the ambient scheme of `D` maps into the image of the ambient scheme of `B`. -/
theorem range_targetHom_le_of_pullbackOpen_eq_top (hqr : pullbackOpen q r = ⊤) :
    Set.range r.targetHom.hom.base ⊆ Set.range q.targetHom.hom.base := by
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ pullbackOpen q r := by rw [hqr]; trivial
  exact hx

/-- The factorization of `r` through the open immersion `q` on ambient schemes, when the open over
which it exists is everything. -/
noncomputable def liftScheme (hqr : pullbackOpen q r = ⊤) :
    D.thickening.target.scheme ⟶ B.thickening.target.scheme :=
  IsOpenImmersion.lift q.targetHom.hom r.targetHom.hom
    (range_targetHom_le_of_pullbackOpen_eq_top q r hqr)

/-- The lift `liftScheme q r hqr` composed with the ambient map of `q` is the ambient map of
`r`. -/
@[reassoc]
theorem liftScheme_targetHom (hqr : pullbackOpen q r = ⊤) :
    liftScheme q r hqr ≫ q.targetHom.hom = r.targetHom.hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- The preimage of an open `U` under `liftScheme q r hqr` is the preimage under the ambient map of
`r` of the image of `U` under the ambient map of `q`. -/
theorem liftScheme_preimage (hqr : pullbackOpen q r = ⊤)
    (U : B.thickening.target.scheme.Opens) :
    liftScheme q r hqr ⁻¹ᵁ U = r.targetHom.hom ⁻¹ᵁ (q.targetHom.hom ''ᵁ U) := by
  rw [← liftScheme_targetHom q r hqr, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]

/-- On sections over an open `U`, `liftScheme q r hqr` is the inverse of the isomorphism given by
the ambient map of `q`, followed by the map of `r` on sections over the image of `U`. -/
theorem liftScheme_app (hqr : pullbackOpen q r = ⊤) (U : B.thickening.target.scheme.Opens)
    (z : Γ(B.thickening.target.scheme, U)) :
    ((liftScheme q r hqr).app U).hom z =
      (D.thickening.target.scheme.presheaf.map
          (eqToHom (liftScheme_preimage q r hqr U)).op).hom
        ((r.targetHom.hom.app (q.targetHom.hom ''ᵁ U)).hom
          ((q.targetHom.hom.appIso U).inv.hom z)) :=
  congrArg (fun m : Γ(B.thickening.target.scheme, U) ⟶
      Γ(D.thickening.target.scheme, liftScheme q r hqr ⁻¹ᵁ U) ↦ m.hom z)
    (IsOpenImmersion.lift_app q.targetHom.hom r.targetHom.hom
      (range_targetHom_le_of_pullbackOpen_eq_top q r hqr) U)

/-- The factorization of `r` through `q` as a morphism of divided power schemes, when the open over
which it exists is everything. -/
noncomputable def liftTarget (hq : IsCartesian q) (hqr : pullbackOpen q r = ⊤) :
    D.thickening.target ⟶ B.thickening.target where
  hom := liftScheme q r hqr
  compatible U := by
    have h := DividedPowers.IsDPMorphism.comp _
      (DividedPowers.IsDPMorphism.comp _
        (D.thickening.target.dividedPowers.naturality
          (eqToHom (liftScheme_preimage q r hqr U)).op)
        (r.targetHom.compatible (q.targetHom.hom ''ᵁ U)))
      (isDPMorphism_appIso_inv q hq U)
    refine Eq.mpr (congrArg _ ?_) h
    exact RingHom.ext fun z ↦ liftScheme_app q r hqr U z

/-- The underlying morphism of schemes of `liftTarget q r hq hqr` is `liftScheme q r hqr`. -/
@[simp]
theorem liftTarget_hom (hq : IsCartesian q) (hqr : pullbackOpen q r = ⊤) :
    (liftTarget q r hq hqr).hom = liftScheme q r hqr := rfl

/-- The lift `liftTarget q r hq hqr` composed with the map of `q` on divided power schemes is the
map of `r` on divided power schemes. -/
@[reassoc]
theorem liftTarget_targetHom (hq : IsCartesian q) (hqr : pullbackOpen q r = ⊤) :
    liftTarget q r hq hqr ≫ q.targetHom = r.targetHom :=
  DividedPowerScheme.Hom.ext (liftScheme_targetHom q r hqr)

/-- The factorization of `r` through `q` on thickened schemes, obtained from the Cartesian square
of `q`. -/
noncomputable def liftSource (hq : IsCartesian q) (hqr : pullbackOpen q r = ⊤) :
    D.thickening.source ⟶ B.thickening.source :=
  hq.lift r.sourceHom (D.thickening.immersion ≫ liftScheme q r hqr) (by
    rw [Category.assoc, liftScheme_targetHom]
    exact r.immersion_naturality.symm)

/-- **The factorization of `r : D ⟶ C` through an open immersion `q : B ⟶ C` of `CRIS(X/S)`**,
when the open of the ambient scheme of `D` over which the factorization exists is everything. -/
noncomputable def liftHomOfTop (hq : IsCartesian q) (hqr : pullbackOpen q r = ⊤) : D ⟶ B where
  sourceHom := liftSource q r hq hqr
  targetHom := liftTarget q r hq hqr
  immersion_naturality := (hq.lift_snd _ _ _).symm
  base_naturality :=
    calc liftTarget q r hq hqr ≫ B.toBase
        = liftTarget q r hq hqr ≫ q.targetHom ≫ C.toBase := by rw [q.base_naturality]
      _ = (liftTarget q r hq hqr ≫ q.targetHom) ≫ C.toBase := (Category.assoc _ _ _).symm
      _ = r.targetHom ≫ C.toBase := by rw [liftTarget_targetHom]
      _ = D.toBase := r.base_naturality
  toX_naturality :=
    calc liftSource q r hq hqr ≫ B.toX
        = liftSource q r hq hqr ≫ q.sourceHom ≫ C.toX := by rw [q.toX_naturality]
      _ = (liftSource q r hq hqr ≫ q.sourceHom) ≫ C.toX := (Category.assoc _ _ _).symm
      _ = r.sourceHom ≫ C.toX := by
            rw [show liftSource q r hq hqr ≫ q.sourceHom = _ from hq.lift_fst _ _ _]
      _ = D.toX := r.toX_naturality

/-- The map of `liftHomOfTop q r hq hqr` on thickened schemes is `liftSource q r hq hqr`. -/
@[simp]
theorem liftHomOfTop_sourceHom (hq : IsCartesian q) (hqr : pullbackOpen q r = ⊤) :
    (liftHomOfTop q r hq hqr).sourceHom = liftSource q r hq hqr := rfl

/-- The map of `liftHomOfTop q r hq hqr` on divided power schemes is `liftTarget q r hq hqr`. -/
@[simp]
theorem liftHomOfTop_targetHom (hq : IsCartesian q) (hqr : pullbackOpen q r = ⊤) :
    (liftHomOfTop q r hq hqr).targetHom = liftTarget q r hq hqr := rfl

/-- **A morphism of `CRIS(X/S)` whose ambient image is covered by that of a Cartesian open
immersion factors through it.** -/
@[reassoc]
theorem liftHomOfTop_comp (hq : IsCartesian q) (hqr : pullbackOpen q r = ⊤) :
    liftHomOfTop q r hq hqr ≫ q = r :=
  Hom.ext (hq.lift_fst _ _ _) (liftTarget_targetHom q r hq hqr)

/-- If `q` is Cartesian and the open over which `r` factors through `q` is everything, then `r`
factors through `q`. -/
theorem exists_lift_of_pullbackOpen_eq_top (hq : IsCartesian q) (hqr : pullbackOpen q r = ⊤) :
    ∃ l : D ⟶ B, l ≫ q = r :=
  ⟨liftHomOfTop q r hq hqr, liftHomOfTop_comp q r hq hqr⟩

end LiftTop

/-- **A Cartesian morphism of `CRIS(X/S)` which is an open immersion on ambient schemes is a
monomorphism.**  Its map on ambient schemes is a monomorphism because an open immersion is, and
its map on thickened schemes is one because it is an open immersion too, being a base change of
the one on ambient schemes. -/
theorem mono_of_isCartesian {A B : Thickening S} {f : A ⟶ B} (hf : IsCartesian f)
    [IsOpenImmersion f.targetHom.hom] : Mono f := by
  have : IsOpenImmersion f.sourceHom := MorphismProperty.of_isPullback hf.flip inferInstance
  refine ⟨fun {Z} g h he ↦ Hom.ext ?_ (DividedPowerScheme.Hom.ext ?_)⟩
  · exact (cancel_mono f.sourceHom).1 (congrArg Hom.sourceHom he)
  · exact (cancel_mono f.targetHom.hom).1 (congrArg (fun k ↦ (Hom.targetHom k).hom) he)

end Thickening

namespace CrystallineThickening

/-- The inclusion `Cris(X/S) ⥤ CRIS(X/S)` creates the finite limits that exist in `CRIS(X/S)`: a
finite diagram of divided power thickenings of `X` whose maps to `X` are open immersions has a
limit in `Cris(X/S)` as soon as it has one in `CRIS(X/S)`, and that limit is computed in
`CRIS(X/S)`.

This is the shape-by-shape tool for the first assertion of [Stacks, Tag 07IJ].  The assertion
itself, with the existence of the limit in `CRIS(X/S)` supplied rather than assumed, is
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.ιCreatesLimitOfNonempty` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/SmallNonemptyFiniteLimits.lean`. -/
@[instance_reducible]
noncomputable def ιCreatesLimit (S : GlobalCrystallineSituation.{u})
    (J : Type) [SmallCategory J] [FinCategory J]
    (F : J ⥤ CrystallineThickening S) [HasLimit (F ⋙ ι S)] :
    CreatesLimit F (ι S) :=
  Limits.createsLimitFullSubcategoryInclusionOfClosed J _ F

/-! ### Cocontinuity -/

/-- **Cover lifting for the inclusion `Cris(X/S) ⥤ CRIS(X/S)`, for a sieve refined by a family of
restrictions.**  If a sieve on the image of `A` contains the images of the restrictions of `A` to
a family of opens covering its ambient scheme, then its pullback along the inclusion is a
covering sieve of `A` in the small crystalline site. -/
theorem ι_functorPullback_mem_smallTopology {A : CrystallineThickening S}
    {T : Sieve ((ι S).obj A)} {ι' : Type (u + 1)}
    (V : ι' → A.obj.thickening.target.scheme.Opens)
    (hV : ∀ x : A.obj.thickening.target.scheme, ∃ i, x ∈ V i)
    (hVT : ∀ i, T.arrows ((ι S).map (A.restrictOpenHom (V i)))) :
    Sieve.functorPullback (ι S) T ∈ smallTopology S A := by
  refine (smallTopology S).superset_covering ?_
    (smallZariskiCovering_mem_smallTopology S (A.restrictOpenCover V)
      (isZariskiCovering_restrictOpenCover A V hV))
  rw [Sieve.generate_le_iff]
  rintro W m ⟨i⟩
  exact hVT i

/-- **Cover lifting for the inclusion `Cris(X/S) ⥤ CRIS(X/S)`.**  Let `{Bᵢ ⟶ B}` be a Zariski
covering family of `CRIS(X/S)` and let `p` be a morphism from the image of `A` to `B`.  The
restrictions of `A` to the opens `p⁻¹(Tᵢ)` of its ambient scheme form a Zariski covering family
of `A` in `Cris(X/S)`, and each member factors through `Bᵢ`; so the pullback along `p` of the
sieve generated by the family pulls back along the inclusion to a covering sieve of `A`. -/
theorem ι_functorPullback_pullback_mem_smallTopology {A : CrystallineThickening S}
    {B : Thickening S} (p : (ι S).obj A ⟶ B) (E : PreZeroHypercover.{u + 1} B)
    (hE : Thickening.IsZariskiCovering E) :
    Sieve.functorPullback (ι S) ((Sieve.generate E.presieve₀).pullback p) ∈
      smallTopology S A := by
  have hE' : (∀ x, ∃ i, x ∈ Set.range ((E.f i).targetHom.hom).base) ∧
      ∀ i, IsOpenImmersion (E.f i).targetHom.hom := by
    simpa only [Thickening.targetPresieve, Scheme.ofArrows_mem_precoverage_iff] using hE.2
  refine ι_functorPullback_mem_smallTopology
    (fun i ↦ have := hE'.2 i; Thickening.pullbackOpen (E.f i) p) (fun x ↦ ?_) fun i ↦ ?_
  · obtain ⟨i, y, hy⟩ := hE'.1 (p.targetHom.hom.base x)
    exact ⟨i, y, hy⟩
  · have := hE'.2 i
    exact ⟨E.X i, Thickening.pullbackLiftHom (E.f i) p (hE.1 i), E.f i, ⟨i⟩,
      Thickening.pullbackLiftHom_comp (E.f i) p (hE.1 i)⟩

/-- **Stacks Project, Tag 07IJ.**  The inclusion `Cris(X/S) ⥤ CRIS(X/S)` is cocontinuous for the
Zariski topologies of the two crystalline sites. -/
@[stacks 07IJ "the inclusion is cocontinuous"]
instance ι_isCocontinuous :
    (ι S).IsCocontinuous (smallTopology S) (topology S) :=
  Functor.isCocontinuous_toGrothendieck _ _ _ fun A _ p R hR ↦ by
    obtain ⟨E, rfl, hE⟩ := hR
    exact ι_functorPullback_pullback_mem_smallTopology p E hE

/-! ### Continuity -/

/-- **The Zariski covering families of `Cris(X/S)`, as a coverage.**  A Zariski covering family of
`B` pulled back along a morphism `p : A ⟶ B` of `Cris(X/S)` is refined by the restrictions of `A`
to the opens of its ambient scheme over which `p` factors through the members of the family. -/
def smallCoverage (S : GlobalCrystallineSituation.{u}) : Coverage (CrystallineThickening S) where
  toPrecoverage := smallPrecoverage S
  pullback := by
    rintro B A p R ⟨E, rfl, hE⟩
    have hcart : ∀ i, Thickening.IsCartesian (E.f i).hom := hE.1
    have hE2 := hE.2
    simp only [Thickening.targetPresieve, Scheme.ofArrows_mem_precoverage_iff] at hE2
    have hsurj : ∀ x : B.obj.thickening.target.scheme,
        ∃ i, ∃ y, (E.f i).hom.targetHom.hom.base y = x := hE2.1
    have hoi : ∀ i, IsOpenImmersion (E.f i).hom.targetHom.hom := hE2.2
    refine ⟨(A.restrictOpenCover
      (fun i ↦ have := hoi i; Thickening.pullbackOpen (E.f i).hom p.hom)).presieve₀,
      ⟨_, rfl, ?_⟩, ?_⟩
    · refine isZariskiCovering_restrictOpenCover _ _ fun x ↦ ?_
      obtain ⟨i, y, hy⟩ := hsurj (p.hom.targetHom.hom.base x)
      exact ⟨i, y, hy⟩
    · rintro Z m ⟨i⟩
      have := hoi i
      exact ⟨E.X i,
        ObjectProperty.homMk (Thickening.pullbackLiftHom (E.f i).hom p.hom (hE.1 i)),
        E.f i, ⟨i⟩,
        ObjectProperty.hom_ext _ (Thickening.pullbackLiftHom_comp (E.f i).hom p.hom (hE.1 i))⟩

/-- **The Zariski topology of the small crystalline site is the topology generated by the coverage
of Zariski covering families.** -/
theorem smallTopology_eq_coverage_toGrothendieck (S : GlobalCrystallineSituation.{u}) :
    smallTopology S = (smallCoverage S).toGrothendieck := by
  show (smallCoverage S).toPrecoverage.toGrothendieck = (smallCoverage S).toGrothendieck
  exact Coverage.toGrothendieck_toPrecoverage (smallCoverage S)

/-- **A commuting square in `CRIS(X/S)` over an object of `Cris(X/S)` whose two legs belong to a
Zariski covering family of `Cris(X/S)` is dominated by a square with vertex in `Cris(X/S)`.**
The dominating object is the restriction of the `i`-th member of the family to the open over which
it factors through the `j`-th one, and the vertex of the given square maps to it because its
ambient scheme lands in that open.  So a family of sections of a presheaf on the big crystalline
site which is compatible over the vertices of `Cris(X/S)` is compatible over all of them. -/
theorem map_eq_of_zariskiCovering_comm {A : CrystallineThickening S}
    {E : PreZeroHypercover.{u + 1} A} (hE : IsZariskiCovering E)
    {G : (Thickening S)ᵒᵖ ⥤ Type (u + 1)}
    (x : ∀ i, G.obj (Opposite.op ((ι S).obj (E.X i))))
    (hx : ∀ (i j : E.I₀) (Z : CrystallineThickening S) (m₁ : Z ⟶ E.X i) (m₂ : Z ⟶ E.X j),
      m₁ ≫ E.f i = m₂ ≫ E.f j →
        G.map ((ι S).map m₁).op (x i) = G.map ((ι S).map m₂).op (x j))
    (i j : E.I₀) {W : Thickening S} (q₁ : W ⟶ (E.X i).obj) (q₂ : W ⟶ (E.X j).obj)
    (hq : q₁ ≫ (E.f i).hom = q₂ ≫ (E.f j).hom) :
    G.map q₁.op (x i) = G.map q₂.op (x j) := by
  have hE2 := hE.2
  simp only [Thickening.targetPresieve, Scheme.ofArrows_mem_precoverage_iff] at hE2
  have hoij : IsOpenImmersion (E.f j).hom.targetHom.hom := hE2.2 j
  have hoiV₀ : IsOpenImmersion ((E.X i).obj.restrictOpenHom
      (Thickening.pullbackOpen (E.f j).hom (E.f i).hom)).targetHom.hom :=
    inferInstanceAs (IsOpenImmersion
      ((E.X i).obj.thickening.target.restrictι
        (Thickening.pullbackOpen (E.f j).hom (E.f i).hom)).hom)
  -- The two legs of the dominating square.
  have hm : (E.X i).restrictOpenHom (Thickening.pullbackOpen (E.f j).hom (E.f i).hom) ≫ E.f i =
      ObjectProperty.homMk
          (Thickening.pullbackLiftHom (E.f j).hom (E.f i).hom (hE.1 j)) ≫ E.f j :=
    ObjectProperty.hom_ext _
      (Thickening.pullbackLiftHom_comp (E.f j).hom (E.f i).hom (hE.1 j)).symm
  have key := hx i j _ _ _ hm
  -- The vertex maps into the dominating object: its ambient scheme lands in the open.
  have htop : Thickening.pullbackOpen ((E.X i).obj.restrictOpenHom
      (Thickening.pullbackOpen (E.f j).hom (E.f i).hom)) q₁ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hbase : (E.f i).hom.targetHom.hom.base (q₁.targetHom.hom.base y)
        = (E.f j).hom.targetHom.hom.base (q₂.targetHom.hom.base y) := by
      have h := congrArg (fun k : W ⟶ A.obj ↦ k.targetHom.hom.base y) hq
      simpa using h
    exact ⟨⟨q₁.targetHom.hom.base y, q₂.targetHom.hom.base y, hbase.symm⟩, rfl⟩
  obtain ⟨c, hc₁⟩ := Thickening.exists_lift_of_pullbackOpen_eq_top
    ((E.X i).obj.restrictOpenHom (Thickening.pullbackOpen (E.f j).hom (E.f i).hom)) q₁
    ((E.X i).obj.isCartesian_restrictOpenHom _) htop
  have hstep : Thickening.pullbackLiftHom (E.f j).hom (E.f i).hom (hE.1 j) ≫ (E.f j).hom =
      (E.X i).obj.restrictOpenHom (Thickening.pullbackOpen (E.f j).hom (E.f i).hom) ≫
        (E.f i).hom :=
    Thickening.pullbackLiftHom_comp (E.f j).hom (E.f i).hom (hE.1 j)
  have hc₂ : c ≫ Thickening.pullbackLiftHom (E.f j).hom (E.f i).hom (hE.1 j) = q₂ := by
    have : Mono (E.f j).hom := Thickening.mono_of_isCartesian (hE.1 j)
    refine (cancel_mono (E.f j).hom).1 ?_
    calc (c ≫ Thickening.pullbackLiftHom (E.f j).hom (E.f i).hom (hE.1 j)) ≫ (E.f j).hom
        = c ≫ Thickening.pullbackLiftHom (E.f j).hom (E.f i).hom (hE.1 j) ≫ (E.f j).hom :=
          Category.assoc _ _ _
      _ = c ≫ (E.X i).obj.restrictOpenHom
            (Thickening.pullbackOpen (E.f j).hom (E.f i).hom) ≫ (E.f i).hom :=
          congrArg (fun k ↦ c ≫ k) hstep
      _ = (c ≫ (E.X i).obj.restrictOpenHom
            (Thickening.pullbackOpen (E.f j).hom (E.f i).hom)) ≫ (E.f i).hom :=
          (Category.assoc _ _ _).symm
      _ = q₁ ≫ (E.f i).hom := congrArg (fun k ↦ k ≫ (E.f i).hom) hc₁
      _ = q₂ ≫ (E.f j).hom := hq
  rw [← hc₁, ← hc₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  exact congrArg (G.map c.op) key

/-- **Stacks Project, Tag 07IJ.**  The inclusion `Cris(X/S) ⥤ CRIS(X/S)` is continuous for the
Zariski topologies of the two crystalline sites: the restriction of a sheaf on the big crystalline
site is a sheaf on the small one.  It suffices to check the Zariski covering families of the small
site; such a family is one of the big site, and the sheaf condition transfers because a family of
sections compatible over the vertices lying in `Cris(X/S)` is compatible over all vertices. -/
@[stacks 07IJ "the inclusion is continuous"]
instance ι_isContinuous :
    (ι S).IsContinuous (smallTopology S) (topology S) where
  op_comp_isSheaf_of_types G := by
    rw [smallTopology_eq_coverage_toGrothendieck, Presieve.isSheaf_coverage]
    rintro A R ⟨E, rfl, hE⟩
    have hsheaf : Presieve.IsSheafFor G.obj
        ((E.map (ι S)).presieve₀ : Presieve ((ι S).obj A)) :=
      (Presieve.isSheafFor_iff_generate _).2
        ((isSheaf_iff_isSheaf_of_type _ _).1 G.property _
          (zariskiCovering_mem_topology S (E.map (ι S)) hE))
    have hpreF : ((E.map (ι S)).presieve₀ : Presieve ((ι S).obj A)) =
        Presieve.ofArrows (fun i ↦ (ι S).obj (E.X i)) (fun i ↦ (ι S).map (E.f i)) := rfl
    have hpre : ((E.presieve₀ : Presieve A)) = Presieve.ofArrows E.X E.f := rfl
    rw [hpreF, Presieve.isSheafFor_arrows_iff] at hsheaf
    rw [hpre, Presieve.isSheafFor_arrows_iff]
    intro y hy
    exact hsheaf y fun i j W q₁ q₂ hqq ↦
      map_eq_of_zariskiCovering_comm hE y (fun i j Z m₁ m₂ h ↦ hy i j Z m₁ m₂ h) i j q₁ q₂ hqq

/-! ### The morphism of topoi induced by the inclusion -/

-- The inclusion `Cris(X/S) ⥤ CRIS(X/S)` is fully faithful, being the inclusion of a full
-- subcategory; the library already has this, as the inclusion of the object property cutting
-- out the small crystalline category.
add_to_stacks 07IJ "the inclusion is fully faithful"
  Crystalline.GlobalCrystallineSituation.CrystallineThickening.fullyFaithfulι

/-- **Stacks Project, Tag 07IJ.**  The morphism of topoi
`i : (X/S)_cris ⟶ (X/S)_CRIS` induced by the inclusion `Cris(X/S) ⥤ CRIS(X/S)`: its direct
image `i_*` is the sheaf pushforward along the cocontinuous inclusion and its inverse image
`i^{-1}` is the sheaf pullback `𝒢 ↦ (ι^p 𝒢)^#`, which is left exact. -/
@[stacks 07IJ "the morphism of topoi i induced by the inclusion"]
noncomputable def smallToBigMorphism (S : GlobalCrystallineSituation.{u}) :
    MorphismOfTopoi (smallTopos S) (topos S) where
  pushforward := (ι S).sheafPushforwardCocontinuous
    (Type (u + 1)) (smallTopology S) (topology S)
  inverseImage := (ι S).sheafPullbackCocontinuous
    (Type (u + 1)) (smallTopology S) (topology S)
  adj := (ι S).sheafAdjunctionPullbackCocontinuous
    (Type (u + 1)) (smallTopology S) (topology S)
  preservesFiniteLimits := inferInstance

/-- **Stacks Project, Tag 07IJ.**  The inverse image `i^{-1}` of the inclusion morphism of topoi
is plain restriction of a sheaf on the big crystalline site to the small one: the sheafification
in `i^{-1} = (ι^p\ )^#` is unnecessary because the inclusion is both continuous and cocontinuous.
Restriction is the direct image `π_*` of the retraction, so this is the formula
`π_* = i^{-1}` of the tag. -/
@[stacks 07IJ "π_* = i^{-1}: the inverse image of i is restriction"]
noncomputable def inverseImageIsoRestriction
    (S : GlobalCrystallineSituation.{u}) :
    (smallToBigMorphism S).inverseImage ≅
      (ι S).sheafPushforwardContinuous (Type (u + 1)) (smallTopology S) (topology S) :=
  (ι S).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) (smallTopology S) (topology S)

/-- The lower shriek `i_!` along the inclusion of the small crystalline site, left adjoint to
restriction `i^{-1}`.  It is the inverse image `π^{-1}` of the retraction of the tag. -/
noncomputable def ιSheafAdjunctionLowerShriek (S : GlobalCrystallineSituation.{u}) :
    Functor.sheafPullbackConstruction.sheafPullback (ι S) (Type (u + 1))
        (smallTopology S) (topology S) ⊣
      (ι S).sheafPushforwardContinuous (Type (u + 1)) (smallTopology S) (topology S) :=
  (ι S).sheafAdjunctionLowerShriek (Type (u + 1)) (smallTopology S) (topology S)

/-- **Stacks Project, Tag 07IJ.**  The composite `π ∘ i` is the identity, on inverse images: the
unit `𝟭 ⟶ i_! ⋙ i^{-1}` of the lower shriek adjunction is an isomorphism, the inclusion being
continuous, cocontinuous and fully faithful.  Since `π^{-1} = i_!` and `π_* = i^{-1}`, this is the
inverse image of the composite `(X/S)_cris ⟶ (X/S)_CRIS ⟶ (X/S)_cris`. -/
@[stacks 07IJ "the composite π ∘ i is the identity, on inverse images"]
noncomputable def lowerShriekRestrictionIsoId (S : GlobalCrystallineSituation.{u}) :
    𝟭 (smallTopos S) ≅
      Functor.sheafPullbackConstruction.sheafPullback (ι S) (Type (u + 1))
          (smallTopology S) (topology S) ⋙
        (ι S).sheafPushforwardContinuous (Type (u + 1)) (smallTopology S) (topology S) :=
  haveI := Functor.isIso_unit_of_sheafPushforwardContinuous (ι S) (Type (u + 1))
    (smallTopology S) (topology S) (ιSheafAdjunctionLowerShriek S)
  asIso (ιSheafAdjunctionLowerShriek S).unit

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation

end
