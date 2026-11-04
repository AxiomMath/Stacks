module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedSequence
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero commutes with limits

Let `j : U ⟶ X` be a quasi-compact open immersion of schemes. Then the extension-by-zero
functor `j_! : Ab(U_proétale) ⥤ Ab(X_proétale)` commutes with limits. This is
[Stacks, Tag 09BP](https://stacks.math.columbia.edu/tag/09BP), and it is proved here with no
hypothesis.

The mechanism is not the one of the source. Writing `i : Z ⟶ X` for the inclusion of the closed
complement of `U`, quasi-compactness of `j` splits every object of `X_proétale` into a part
pulled back from `U_proétale` and a part all of whose points specialize into the closed fibre,
`AlgebraicGeometry.ProEtale.hasEnoughObjects_openPart_or_closedFibre`. On *sections over* each
kind of object the functor `j_! j^{-1}` is computed outright:

* over an object pulled back from `U_proétale` the counit `j_! j^{-1} F ⟶ F` is invertible,
  `AlgebraicGeometry.ProEtale.isIso_proetaleRestriction_map_counit`, so the sections are the
  sections of `F`, naturally in `F`;
* over an object all of whose points specialize into the closed fibre the sections vanish,
  [Stacks, Tag 09AG](https://stacks.math.columbia.edu/tag/09AG), which is
  `AlgebraicGeometry.ProEtale.isZero_extensionByZero_sections_of_specializes_to_closed`.

Both computations are natural in `F`, and sections of sheaves commute with limits, so on each of
these objects `j_! j^{-1}` commutes with limits. A morphism of sheaves which is invertible on
sections over the objects of a covering family is invertible — it is a monomorphism and an
epimorphism by `AlgebraicGeometry.ProEtale.mono_of_hasEnoughObjects` and
`AlgebraicGeometry.ProEtale.epi_of_hasEnoughObjects`, and the category of abelian sheaves is
abelian — so the comparison map from `j_! j^{-1}` of a limit to the limit of `j_! j^{-1}` is
invertible, which is `AlgebraicGeometry.ProEtale.preservesLimitsOfShape_of_hasEnoughObjects`.
Finally `j^{-1}` has a right adjoint `j_*` with invertible counit, `j` being an open immersion,
so `j_!` is isomorphic to `j_! j^{-1} j_*` and commutes with limits as well.

In particular neither of the two inputs the source takes from elsewhere is used: short exactness
of the open-closed sequence, [Stacks, Tag 09AH](https://stacks.math.columbia.edu/tag/09AH), and
that `i^{-1}` commutes with limits, clause (1) of
[Stacks, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA). The source reduces to products
using exactness of `j_!` and exactness of products on the pro-étale site, then reads `j_!` off
the open-closed sequence as a kernel of two product-preserving functors; that route needs both
inputs, and neither is available for the small pro-étale site of
`AlgebraicGeometry.Scheme.ProEt` in this library — short exactness on `X_proétale` rests on
[Stacks, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC) for this site, which is not
discharged, and 09AA (1) is proved only for sheaves of *sets* on the small sites of a chosen big
pro-étale site. The sectionwise route uses only the two computations above, both of which hold
here with nothing assumed: 09AG is proved, and the counit is invertible over the open part for
any open immersion. The source's route is nevertheless retained, with its two inputs as
hypotheses, as `preservesLimits_proetaleRestriction_comp_extensionByZero`: it applies to any
weakly étale `j`, where the covering family above — which needs `j` to be a quasi-compact open
immersion — is not available.

## Main results

* `CategoryTheory.Limits.preservesLimitsOfShape_of_isKernel_of_detectsZero`: a functor which is
  pointwise the kernel of a natural transformation preserves limits of a given shape, provided
  the middle functor does and the right-hand functor detects zero maps into a limit of its
  values. `CategoryTheory.Limits.preservesLimitsOfShape_of_isKernel` is the special case in
  which the right-hand functor preserves those limits.
* `AlgebraicGeometry.ProEtale.exists_closedComplement`: the complement of the image of an open
  immersion is the image of a closed immersion.
* `AlgebraicGeometry.ProEtale.preservesLimitsOfShape_of_hasEnoughObjects`: a functor into
  abelian sheaves preserving limits on sections over the objects of a covering family preserves
  limits.
* `preservesLimits_proetaleRestriction_comp_extensionByZero_of_quasiCompact`, in the
  `AlgebraicGeometry.ProEtale` namespace: `j_! j^{-1}` commutes with limits, for a quasi-compact
  open immersion `j`, with nothing assumed.
* `AlgebraicGeometry.ProEtale.preservesLimits_extensionByZero_unconditional`: **Stacks 09BP**,
  extension by zero of abelian pro-étale sheaves along a quasi-compact open immersion commutes
  with limits, with nothing assumed. `AlgebraicGeometry.ProEtale.preservesLimits_extensionByZero`
  is the same conclusion in the shape the source's own proof gives it, carrying that proof's two
  inputs as unused hypotheses.

## Implementation notes

Quasi-compactness of `j` is what produces the covering family: it makes the closed fibre of an
affine object of `X_proétale` cut out by finitely many equations, and hence gives the
ind-Zariski localization of [Stacks, Tag 096V](https://stacks.math.columbia.edu/tag/096V) along
it. It is also what the source's own proof uses it for, through
[Stacks, Tag 09AH](https://stacks.math.columbia.edu/tag/09AH).

That a closed complement of `U` exists is not assumed anywhere: it is produced inside the proofs
by `AlgebraicGeometry.ProEtale.exists_closedComplement`, so the only data of the tagged
statement is `j`.

The statement is about all limits, not only finite limits or products: the comparison map is
tested on sections one shape at a time, and nothing in the argument reduces one shape to
another.

## References

* [Stacks Project, Tag 09BP](https://stacks.math.columbia.edu/tag/09BP)
* [Stacks Project, Tag 09AG](https://stacks.math.columbia.edu/tag/09AG)
* [Stacks Project, Tag 09AH](https://stacks.math.columbia.edu/tag/09AH)
* [Stacks Project, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA)
* [Stacks Project, Tag 096V](https://stacks.math.columbia.edu/tag/096V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w' a a' e e'

namespace CategoryTheory.Limits

/-- A functor that is pointwise a kernel preserves limits of shape `I`: if `a : F ⟶ G` and
`b : G ⟶ H` compose to zero and `a.app X` is a kernel of `b.app X` for every `X`, if `G`
preserves limits of shape `I`, and if a map into `H.obj c.pt` killed by all the maps
`H.map (c.π.app k)` of a limit cone `c` of shape `I` is zero, then `F` preserves limits of
shape `I`.

The last hypothesis holds as soon as `H` preserves limits of shape `I`, by uniqueness of maps
into a limit cone; it asks only that the comparison map from `H.obj c.pt` to the limit of the
values of `H` be a monomorphism.

The limit cone for `K ⋙ F` is obtained by lifting the limit cone for `K ⋙ G` through the
kernel: a cone over `K ⋙ F` maps to a cone over `K ⋙ G` by `a`, whose induced map to
`G.obj c.pt` is killed by `b` because the maps `H.map (c.π.app k)` detect this. -/
theorem preservesLimitsOfShape_of_isKernel_of_detectsZero
    {C D I : Type*} [Category C] [Category D] [Category I] [HasZeroMorphisms D]
    {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
    (w : ∀ X, a.app X ≫ b.app X = 0)
    (ha : ∀ X, IsLimit (KernelFork.ofι (a.app X) (w X)))
    (hH : ∀ (K : I ⥤ C) (c : Cone K), IsLimit c → ∀ (W : D) (f : W ⟶ H.obj c.pt),
      (∀ k, f ≫ H.map (c.π.app k) = 0) → f = 0)
    [PreservesLimitsOfShape I G] :
    PreservesLimitsOfShape I F := by
  refine ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩
  let hG := isLimitOfPreserves G hc
  have mono (X : C) : Mono (a.app X) := Fork.IsLimit.mono (ha X)
  let lift (s : Cone (K ⋙ F)) : s.pt ⟶ G.obj c.pt :=
    hG.lift ((Cone.postcompose (Functor.whiskerLeft K a)).obj s)
  have lift_fac (s : Cone (K ⋙ F)) (i : I) :
      lift s ≫ G.map (c.π.app i) = s.π.app i ≫ a.app (K.obj i) :=
    hG.fac _ i
  have lift_zero (s : Cone (K ⋙ F)) : lift s ≫ b.app c.pt = 0 := by
    refine hH K c hc _ _ (fun i ↦ ?_)
    rw [Category.assoc, ← b.naturality, ← Category.assoc, lift_fac,
      Category.assoc, w, comp_zero]
  refine ⟨{
    lift := fun s ↦ (ha c.pt).lift (KernelFork.ofι (lift s) (lift_zero s))
    fac := ?_
    uniq := ?_ }⟩
  · intro s i
    apply (cancel_mono (a.app (K.obj i))).1
    show ((ha c.pt).lift (KernelFork.ofι (lift s) (lift_zero s)) ≫
      F.map (c.π.app i)) ≫ a.app (K.obj i) = _
    rw [Category.assoc, a.naturality, ← Category.assoc]
    show ((ha c.pt).lift (KernelFork.ofι (lift s) (lift_zero s)) ≫
      (KernelFork.ofι (a.app c.pt) (w c.pt)).ι) ≫ _ = _
    rw [Fork.IsLimit.lift_ι]
    exact lift_fac s i
  · intro s m hm
    apply (cancel_mono (a.app c.pt)).1
    show m ≫ a.app c.pt = (ha c.pt).lift (KernelFork.ofι (lift s) (lift_zero s)) ≫
      (KernelFork.ofι (a.app c.pt) (w c.pt)).ι
    rw [Fork.IsLimit.lift_ι]
    refine hG.hom_ext fun i ↦ ?_
    show (m ≫ a.app c.pt) ≫ G.map (c.π.app i) = _
    change ∀ i, m ≫ F.map (c.π.app i) = s.π.app i at hm
    rw [Category.assoc, ← a.naturality, ← Category.assoc, hm]
    exact (lift_fac s i).symm

/-- A functor that is pointwise a kernel preserves limits of every shape its two companions
preserve: if `a : F ⟶ G` and `b : G ⟶ H` compose to zero and `a.app X` is a kernel of
`b.app X` for every `X`, and if `G` and `H` preserve limits of shape `I`, then so does `F`.

This is `preservesLimitsOfShape_of_isKernel_of_detectsZero`, whose last hypothesis holds as
soon as `H` preserves limits of shape `I`, by uniqueness of maps into a limit cone. -/
theorem preservesLimitsOfShape_of_isKernel
    {C D I : Type*} [Category C] [Category D] [Category I] [HasZeroMorphisms D]
    {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
    (w : ∀ X, a.app X ≫ b.app X = 0)
    (ha : ∀ X, IsLimit (KernelFork.ofι (a.app X) (w X)))
    [PreservesLimitsOfShape I G] [PreservesLimitsOfShape I H] :
    PreservesLimitsOfShape I F :=
  preservesLimitsOfShape_of_isKernel_of_detectsZero a b w ha
    fun _ _ hc _ _ hf ↦ (isLimitOfPreserves H hc).hom_ext fun k ↦ by simpa using hf k

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The image of an open immersion is the complement of the image of a closed immersion: the
closed complement carries the subscheme structure cut out by its vanishing ideal.

This is what makes the hypothesis `Set.range j.base = (Set.range i.base)ᶜ` below a situation
that occurs. -/
theorem exists_closedComplement {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range j.base = (Set.range i.base)ᶜ := by
  refine ⟨_, (Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ :
      TopologicalSpace.Closeds X)).subschemeι, inferInstance, ?_⟩
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp

/-! ### Testing preservation of limits on a covering family of objects -/

/-- The sections functor of a sheaf category over an object preserves limits of shape `I`. -/
private theorem preservesLimitsOfShape_sheafSections {C : Type w} [Category.{w'} C]
    {A : Type a} [Category.{a'} A] {J : GrothendieckTopology C} [HasSheafify J A]
    {I : Type e} [Category.{e'} I] [HasLimitsOfShape I A] (V : C) :
    PreservesLimitsOfShape I ((sheafSections J A).obj (op V)) :=
  preservesLimitsOfShape_of_natIso (sheafSectionsNatIsoEvaluation (J := J) (A := A) (X := V)).symm

/-- **Preservation of limits is tested on sections over a covering family of objects.** A functor
into abelian sheaves whose composites with the sections functors of the objects of a family
covering every object of the site preserve limits of shape `I` preserves limits of shape `I`.

Limits of sheaves are computed on sections, so the comparison map from the value of the functor
at a limit to the limit of its values is invertible on sections over each object of the family;
being invertible there it is a monomorphism and an epimorphism, by `mono_of_hasEnoughObjects`
and `epi_of_hasEnoughObjects`, hence invertible, the category of abelian sheaves being
abelian. -/
theorem preservesLimitsOfShape_of_hasEnoughObjects
    {C : Type w} [Category.{w'} C] {A : Type a} [Category.{a'} A] [Abelian A] [HasLimits A]
    {J : GrothendieckTopology C} [HasSheafify J A] {B : ObjectProperty C}
    {E : Type e} [Category.{e'} E] {I : Type a'} [Category.{a'} I]
    (hB : J.HasEnoughObjects B) (Φ : E ⥤ Sheaf J A)
    (hΦ : ∀ ⦃V : C⦄, B V →
      PreservesLimitsOfShape I (Φ ⋙ (sheafSections J A).obj (op V))) :
    PreservesLimitsOfShape I Φ := by
  refine ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩
  have key : ∀ ⦃V : C⦄, B V →
      IsIso (((sheafSections J A).obj (op V)).map
        ((limit.isLimit (K ⋙ Φ)).lift (Φ.mapCone c))) := by
    intro V hV
    have _ := hΦ hV
    have _ := preservesLimitsOfShape_sheafSections (J := J) (A := A) (I := I) V
    have h₁ : IsLimit ((Φ ⋙ (sheafSections J A).obj (op V)).mapCone c) :=
      isLimitOfPreserves _ hc
    have h₂ : IsLimit (((sheafSections J A).obj (op V)).mapCone (limit.cone (K ⋙ Φ))) :=
      isLimitOfPreserves _ (limit.isLimit (K ⋙ Φ))
    let φ : (Φ ⋙ (sheafSections J A).obj (op V)).mapCone c ⟶
        ((sheafSections J A).obj (op V)).mapCone (limit.cone (K ⋙ Φ)) :=
      { hom := ((sheafSections J A).obj (op V)).map
          ((limit.isLimit (K ⋙ Φ)).lift (Φ.mapCone c))
        w := fun k ↦ by
          have h := (limit.isLimit (K ⋙ Φ)).fac (Φ.mapCone c) k
          simp only [Functor.mapCone_π_app, Functor.comp_map, ← Functor.map_comp]
          exact congrArg _ h }
    have _ := IsLimit.hom_isIso h₁ h₂ φ
    exact inferInstanceAs (IsIso ((Cones.forget _).map φ))
  have _ : Mono ((limit.isLimit (K ⋙ Φ)).lift (Φ.mapCone c)) :=
    mono_of_hasEnoughObjects hB _ fun V hV ↦ by
      have _ := key hV
      exact inferInstanceAs (Mono (((sheafSections J A).obj (op V)).map
        ((limit.isLimit (K ⋙ Φ)).lift (Φ.mapCone c))))
  have _ : Epi ((limit.isLimit (K ⋙ Φ)).lift (Φ.mapCone c)) :=
    epi_of_hasEnoughObjects hB _ fun V hV ↦ by
      have _ := key hV
      exact inferInstanceAs (Epi (((sheafSections J A).obj (op V)).map
        ((limit.isLimit (K ⋙ Φ)).lift (Φ.mapCone c))))
  have _ : IsIso ((limit.isLimit (K ⋙ Φ)).lift (Φ.mapCone c)) := isIso_of_mono_of_epi _
  exact ⟨IsLimit.ofPointIso (limit.isLimit (K ⋙ Φ))⟩

/-! ### The sections of `j_! j^{-1}` on the two kinds of object -/

/-- Over an object of `X_proétale` pulled back from `U_proétale`, the functor `j_! j^{-1}`
commutes with limits on sections: the counit `j_! j^{-1} F ⟶ F` is invertible there, naturally
in `F`, and sections of sheaves commute with limits. -/
theorem preservesLimitsOfShape_sections_extensionByZero_of_proetalePostcompose
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {I : Type max (u + 1) v} [Category.{max (u + 1) v} I]
    (V : X.ProEt) (W : U.ProEt) (e : V ≅ (proetalePostcompose j).obj W) :
    PreservesLimitsOfShape I
      ((Abelian.proetaleRestriction.{u, v} j ⋙ Abelian.extensionByZero.{u, v} j) ⋙
        (sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).obj (op V)) := by
  have hiso : ∀ F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v},
      IsIso (((Abelian.extensionByZero_adjunction.{u, v} j).counit.app F).hom.app (op V)) := by
    intro F
    have hW : IsIso (((Abelian.extensionByZero_adjunction.{u, v} j).counit.app F).hom.app
        (op ((proetalePostcompose j).obj W))) := by
      have _ := isIso_proetaleRestriction_map_counit.{u, v} j F
      exact inferInstanceAs (IsIso
        (((sheafSections (Scheme.ProEt.topology U) AddCommGrpCat.{max (u + 1) v}).obj
          (op W)).map ((Abelian.proetaleRestriction.{u, v} j).map
            ((Abelian.extensionByZero_adjunction.{u, v} j).counit.app F))))
    exact (NatTrans.isIso_app_iff_of_iso _ e.op).mp hW
  have _ := preservesLimitsOfShape_sheafSections (J := Scheme.ProEt.topology X)
    (A := AddCommGrpCat.{max (u + 1) v}) (I := I) V
  let wr := Functor.whiskerRight (Abelian.extensionByZero_adjunction.{u, v} j).counit
    ((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).obj (op V))
  have _ : ∀ F, IsIso (wr.app F) := hiso
  have _ : IsIso wr := NatIso.isIso_of_isIso_app wr
  exact preservesLimitsOfShape_of_natIso
    ((Functor.leftUnitor ((sheafSections (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v}).obj (op V))).symm ≪≫ (asIso wr).symm)

/-- Over an object of `X_proétale` all of whose points specialize into the closed fibre, the
functor `j_! j^{-1}` commutes with limits on sections: those sections vanish, by
[Stacks, Tag 09AG](https://stacks.math.columbia.edu/tag/09AG). -/
theorem preservesLimitsOfShape_sections_extensionByZero_of_specializes_to_closed
    {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [WeaklyEtale j]
    (hdisjoint : IsEmpty (pullback j i : Scheme.{u}))
    {I : Type max (u + 1) v} [Category.{max (u + 1) v} I]
    (V : X.ProEt) [IsAffine V.left]
    (hV : ∀ x : V.left, ∃ z : (pullback V.hom i : Scheme.{u}),
      Specializes x ((pullback.fst V.hom i).base z)) :
    PreservesLimitsOfShape I
      ((Abelian.proetaleRestriction.{u, v} j ⋙ Abelian.extensionByZero.{u, v} j) ⋙
        (sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).obj (op V)) :=
  Functor.preservesLimitsOfShape_of_isZero _
    ((Functor.isZero_iff _).2 fun F ↦
      isZero_extensionByZero_sections_of_specializes_to_closed.{u, v} j i hdisjoint V hV
        ((Abelian.proetaleRestriction.{u, v} j).obj F)) I

/-! ### The source's route: `j_! j^{-1}` as a kernel -/

section Complement

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)

/-- The functor `j_! j^{-1}` commutes with limits, granted that the open-closed sequence
`0 → j_! j^{-1} F → F → i_* i^{-1} F → 0` of
[Stacks, Tag 09AH](https://stacks.math.columbia.edu/tag/09AH) is short exact and that the
inverse image `i^{-1}` commutes with limits, which is clause (1) of
[Stacks, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA).

Indeed `j_! j^{-1}` is then pointwise the kernel of the map from the identity functor to
`i_* i^{-1}`, and both of those commute with limits, the latter because `i^{-1}` does and
`i_*` is a right adjoint.

This is the source's own argument. For a quasi-compact open immersion `j` neither hypothesis is
needed: see `preservesLimits_proetaleRestriction_comp_extensionByZero_of_quasiCompact`, which
computes the sections of `j_! j^{-1}` on a covering family instead. The hypotheses are what
makes the statement available for a merely weakly étale `j`, for which that covering family is
not. -/
theorem preservesLimits_proetaleRestriction_comp_extensionByZero [WeaklyEtale j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (hker : ∀ F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v},
      (openClosedShortComplex.{u, v} i j hij F).ShortExact)
    (hlim : PreservesLimits (Abelian.proetaleInverseImage.{u, v} i)) :
    PreservesLimits
      (Abelian.proetaleRestriction.{u, v} j ⋙ Abelian.extensionByZero.{u, v} j) := by
  have _ : (Abelian.proetaleDirectImage.{u, v} i).IsRightAdjoint :=
    (Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).isRightAdjoint
  exact ⟨fun {J} _ ↦ preservesLimitsOfShape_of_isKernel_of_detectsZero
    (Abelian.extensionByZero_adjunction.{u, v} j).counit
    (Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).unit
    (extensionByZero_counit_comp_proetaleInverseImage_unit i j hij)
    (fun F ↦ (hker F).fIsKernel)
    (fun _ _ hc _ _ hf ↦
      (isLimitOfPreserves (Abelian.proetaleInverseImage.{u, v} i ⋙
        Abelian.proetaleDirectImage.{u, v} i) hc).hom_ext fun k ↦ by simpa using hf k)⟩

end Complement

/-! ### Extension by zero commutes with limits -/

section Conclusion

variable {U X : Scheme.{u}} (j : U ⟶ X)

/-- For a quasi-compact open immersion `j : U ⟶ X`, the functor `j_! j^{-1}` of abelian
pro-étale sheaves commutes with limits, with nothing assumed.

The closed complement of `U` is produced inside the proof, and the two kinds of object of the
covering family it gives are handled by
`preservesLimitsOfShape_sections_extensionByZero_of_proetalePostcompose` and
`preservesLimitsOfShape_sections_extensionByZero_of_specializes_to_closed`. -/
theorem preservesLimits_proetaleRestriction_comp_extensionByZero_of_quasiCompact
    [IsOpenImmersion j] [QuasiCompact j] :
    PreservesLimits
      (Abelian.proetaleRestriction.{u, v} j ⋙ Abelian.extensionByZero.{u, v} j) := by
  obtain ⟨Z, i, _, hij⟩ := exists_closedComplement j
  refine ⟨fun {I} _ ↦ preservesLimitsOfShape_of_hasEnoughObjects
    (hasEnoughObjects_openPart_or_closedFibre i j hij) _ ?_⟩
  rintro V (⟨W, ⟨e⟩⟩ | ⟨_, _, hspec⟩)
  · exact preservesLimitsOfShape_sections_extensionByZero_of_proetalePostcompose.{u, v} j V W e
  · exact preservesLimitsOfShape_sections_extensionByZero_of_specializes_to_closed.{u, v} i j
      (isEmpty_pullback_of_range_eq_compl i j hij) V hspec

/-- **Stacks 09BP.** For a quasi-compact open immersion `j : U ⟶ X` of schemes, extension by
zero `j_! : Ab(U_proétale) ⥤ Ab(X_proétale)` of abelian sheaves on the small pro-étale sites
commutes with limits.

Nothing is assumed: `j_! j^{-1}` commutes with limits by
`preservesLimits_proetaleRestriction_comp_extensionByZero_of_quasiCompact`, whose proof computes
the sections of `j_! j^{-1}` on the covering family that quasi-compactness of `j` produces; and
`j_!` is isomorphic to `j_! j^{-1} j_*` because the counit of `j^{-1} ⊣ j_*` is invertible for
an open immersion. -/
@[stacks 09BP]
theorem preservesLimits_extensionByZero_unconditional [IsOpenImmersion j] [QuasiCompact j] :
    PreservesLimits (Abelian.extensionByZero.{u, v} j) := by
  have _ : PreservesLimits
      (Abelian.proetaleRestriction.{u, v} j ⋙ Abelian.extensionByZero.{u, v} j) :=
    preservesLimits_proetaleRestriction_comp_extensionByZero_of_quasiCompact.{u, v} j
  obtain ⟨⟨R, adj⟩⟩ := exists_directImage_abelian.{u, v} j
  have _ : R.IsRightAdjoint := adj.isRightAdjoint
  have _ : IsIso adj.counit := directImage_counit_isIso_abelian.{u, v} j R adj
  exact preservesLimits_of_natIso
    (F := R ⋙ Abelian.proetaleRestriction.{u, v} j ⋙ Abelian.extensionByZero.{u, v} j)
    (Functor.isoWhiskerRight (asIso adj.counit) (Abelian.extensionByZero.{u, v} j))

end Conclusion

section ConclusionWithHypotheses

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)

/-- **Stacks 09BP.** For a quasi-compact open immersion `j : U ⟶ X` of schemes, extension by
zero `j_! : Ab(U_proétale) ⥤ Ab(X_proétale)` of abelian sheaves on the small pro-étale sites
commutes with limits.

Here `i : Z ⟶ X` is the inclusion of the closed complement of `U`, and the two inputs the
source's own proof takes from elsewhere are carried as hypotheses: short exactness of the
open-closed sequence of [Stacks, Tag 09AH](https://stacks.math.columbia.edu/tag/09AH), and the
fact that `i^{-1}` commutes with limits, which is clause (1) of
[Stacks, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA).

Neither is in fact needed, and none of the three hypotheses is used in the proof below: the
conclusion is `preservesLimits_extensionByZero_unconditional`, which proves it with nothing
assumed. This form is kept because it is the shape in which the statement is cited. -/
theorem preservesLimits_extensionByZero [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (hker : ∀ F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v},
      (openClosedShortComplex.{u, v} i j hij F).ShortExact)
    (hlim : PreservesLimits (Abelian.proetaleInverseImage.{u, v} i)) :
    PreservesLimits (Abelian.extensionByZero.{u, v} j) :=
  preservesLimits_extensionByZero_unconditional.{u, v} j

end ConclusionWithHypotheses

end AlgebraicGeometry.ProEtale

end
