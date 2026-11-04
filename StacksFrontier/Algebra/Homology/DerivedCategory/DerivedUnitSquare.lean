module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ColumnResolution
public import StacksFrontier.Algebra.Homology.TotalComplexShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The derived unit square of a left exact functor

Let `B : 𝒜 ⥤ ℬ` be a left exact additive functor between abelian categories, with `𝒜` having
functorial injective embeddings, and let `RB : D(𝒜) ⥤ D(ℬ)` be a right derived functor of `B`,
computed by K-injective complexes, with unit `u_K : B(K) ⟶ RB(K)`. For a morphism `ρ : K ⟶ M`
of cochain complexes of `𝒜` vanishing in negative degrees, consider the commutative square

```
 B(K) ──B(ρ)──▶ B(M)
  │u_K            │u_M
  ▼               ▼
RB(K) ─RB(ρ)──▶ RB(M)
```

in `D(ℬ)`. **If `ρ` induces isomorphisms `R^qB(K^a) ≅ R^qB(M^a)` for every `a` and every
`q ≥ 1`, then this square is homotopy cartesian**: there is a distinguished triangle

`B(K) ⟶ RB(K) ⊞ B(M) ⟶ RB(M) ⟶ B(K)[1]`

whose first map is `(u_K, B(ρ))` and whose second is `(RB(ρ), -u_M)`.

This is the triangulated form of the following computation: column by column, the cokernels of
`B(K^a) ⟶ RB(K^a)` and of `B(M^a) ⟶ RB(M^a)` have cohomology `R^{≥1}B(K^a)` and `R^{≥1}B(M^a)`,
and `ρ` identifies them; assembling the columns ([Stacks, Tag 0133]) identifies the cokernels of
the two vertical arrows, which is what makes the square homotopy cartesian.

## Main definitions

* `StacksDraft.DerivedUnitSquare.unitQ`: the unit `u_K : B(K) ⟶ RB(K)` read on cochain complexes.

## Main results

* `StacksDraft.DerivedUnitSquare.total_isColimit_cokernelCofork`: the total complex of a
  double complex preserves cokernels.
* `StacksDraft.DerivedUnitSquare.exists_distTriang`: **the square is homotopy cartesian.**
* `StacksDraft.DerivedUnitSquare.exists_distTriang_of_isPushout`: the square pasted with a
  bicartesian square of complexes `A ⟶ B(K) ⊞ N ⟶ B(M)` is homotopy cartesian.

## Implementation notes

The vertical arrows are realised on the nose by a functorial column-by-column injective
resolution `R` (`StacksDraft.ColumnResolution.FunctorialResolution`): `RB(K)` is
`B(Tot R(K)) = Tot B(R(K))`, and `u_K` is the inclusion of the row `B(K) ⊆ B(R(K))^{•,0}`. The
square is then made homotopy cartesian at the level of complexes, by pushing this inclusion
out along `B(ρ)`: the pushout `P` sits in a short exact sequence
`0 ⟶ B(K) ⟶ Tot B(R(K)) ⊞ B(M) ⟶ P ⟶ 0`, and the canonical map `P ⟶ Tot B(R(M))` is a
quasi-isomorphism by the five lemma, because the cokernels of the two inclusions are identified
by the column computation above. No triangulated argument is needed beyond the distinguished
triangle of a short exact sequence.

## References

* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 0141](https://stacks.math.columbia.edu/tag/0141)
-/

@[expose] public noncomputable section

open CategoryTheory Limits ZeroObject HomologicalComplex StacksDraft.TotalComplexQuasiIso

-- The arrows of cochain complexes below must be read through the category structure, not through
-- the reflexive quiver structure every category also carries; otherwise the morphisms built here
-- and the pushouts and short complexes they enter disagree on the `Quiver` instance.
attribute [-instance] CategoryTheory.catToReflQuiver

namespace StacksDraft.DerivedUnitSquare

/-! ### The total complex preserves cokernels -/

section Total

variable {D : Type*} [Category D] [Abelian D]
  {A B : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : A ⟶ B)
  [A.HasTotal (ComplexShape.up ℤ)] [B.HasTotal (ComplexShape.up ℤ)]
  [(cokernel f).HasTotal (ComplexShape.up ℤ)]

/-- Each component of the cokernel of a morphism of double complexes is the cokernel of the
corresponding component. -/
def isColimit_cokernelCofork_f_f (p q : ℤ) :
    IsColimit (CokernelCofork.ofπ (f := (f.f p).f q) ((cokernel.π f).f p |>.f q)
      (by rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, cokernel.condition,
        HomologicalComplex.zero_f, HomologicalComplex.zero_f])) :=
  isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval _ _ p ⋙ HomologicalComplex.eval D (ComplexShape.up ℤ) q) f

/-- **The total complex preserves cokernels**, in each degree. -/
def total_isColimit_cokernelCofork (n : ℤ) :
    IsColimit (CokernelCofork.ofπ (f := (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)).f n)
      ((HomologicalComplex₂.total.map (cokernel.π f) (ComplexShape.up ℤ)).f n)
      (by rw [← HomologicalComplex.comp_f, ← HomologicalComplex₂.total.map_comp,
        cokernel.condition, HomologicalComplex₂.total_map_zero,
        HomologicalComplex.zero_f])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {W} φ hφ => (cokernel f).totalDesc (fun p q h =>
      (isColimit_cokernelCofork_f_f f p q).desc (CokernelCofork.ofπ
        (B.ιTotal (ComplexShape.up ℤ) p q n h ≫ φ) (by
          rw [← Category.assoc, ← HomologicalComplex₂.ιTotal_map, Category.assoc, hφ,
            comp_zero]))))
    (fun {W} φ hφ => by
      refine HomologicalComplex₂.total.hom_ext _ (fun p q h => ?_)
      rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
        HomologicalComplex₂.ι_totalDesc]
      exact (isColimit_cokernelCofork_f_f f p q).fac _ WalkingParallelPair.one)
    (fun {W} φ hφ m hm => by
      refine HomologicalComplex₂.total.hom_ext _ (fun p q h => ?_)
      rw [HomologicalComplex₂.ι_totalDesc]
      refine (isColimit_cokernelCofork_f_f f p q).hom_ext ?_
      rintro (_ | _)
      · simp only [Cofork.app_zero_eq_comp_π_left, CokernelCofork.π_ofπ, ← Category.assoc,
          ← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f, zero_comp]
      · rw [(isColimit_cokernelCofork_f_f f p q).fac _ WalkingParallelPair.one]
        dsimp
        rw [← hm, ← Category.assoc, ← HomologicalComplex₂.ιTotal_map, Category.assoc])

end Total

/-- A morphism between two kernels of the same morphism, compatible with the inclusions, is an
isomorphism. -/
lemma isIso_of_isLimit_kernelFork {D : Type*} [Category D] [HasZeroMorphisms D]
    {X₁ X₂ Y Z : D} {g : Y ⟶ Z} {ι₁ : X₁ ⟶ Y} {ι₂ : X₂ ⟶ Y} {w₁ : ι₁ ≫ g = 0}
    {w₂ : ι₂ ≫ g = 0} (h₁ : IsLimit (KernelFork.ofι ι₁ w₁)) (h₂ : IsLimit (KernelFork.ofι ι₂ w₂))
    (φ : X₁ ⟶ X₂) (hφ : φ ≫ ι₂ = ι₁) : IsIso φ := by
  have : φ = (IsLimit.conePointUniqueUpToIso h₁ h₂).hom := by
    refine Fork.IsLimit.hom_ext h₂ ?_
    simp only [KernelFork.ι_ofι, hφ]
    simpa using (IsLimit.conePointUniqueUpToIso_hom_comp h₁ h₂ WalkingParallelPair.zero).symm
  rw [this]
  infer_instance


/-! ### Pushing out a monomorphism -/

section Pushout

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {X₁ X₂ X₃ Y : 𝒜} (f : X₁ ⟶ X₂) (g : X₁ ⟶ X₃)

/-- The pushout of a monomorphism `f` along `g` gives a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⊞ X₃ ⟶ X₂ ⊔_{X₁} X₃ ⟶ 0`. -/
lemma shortExact_pushout (hf : Mono f) :
    (IsPushout.of_hasPushout f g).toCommSq.shortComplex.ShortExact := by
  have sq := IsPushout.of_hasPushout f g
  have : Mono (biprod.lift f (-g)) := @mono_of_mono_fac _ _ _ _ _ _ _ _ hf (biprod.lift_fst f (-g))
  exact ShortComplex.ShortExact.mk' sq.exact_shortComplex this sq.epi_shortComplex_g

/-- If `0 ⟶ X₁ ⟶ X₂ ⟶ Y ⟶ 0` is short exact, so is `0 ⟶ X₃ ⟶ X₂ ⊔_{X₁} X₃ ⟶ Y ⟶ 0`: a pushout
does not change the cokernel. -/
lemma shortExact_pushout_inr (π : X₂ ⟶ Y) (w : f ≫ π = 0)
    (hS : (ShortComplex.mk f π w).ShortExact) :
    (ShortComplex.mk (pushout.inr f g) (pushout.desc π 0 (by rw [comp_zero, w]))
      (pushout.inr_desc _ _ _)).ShortExact := by
  have hf : Mono f := hS.mono_f
  have sq := IsPushout.of_hasPushout f g
  have hmono : Mono (pushout.inr f g) :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (P := MorphismProperty.monomorphisms _) sq.flip hf
  have hπ : Epi π := hS.epi_g
  have hepi : Epi (pushout.desc (f := f) (g := g) π (0 : X₃ ⟶ Y) (by rw [comp_zero, w])) :=
    epi_of_epi_fac (pushout.inl_desc (f := f) (g := g) π (0 : X₃ ⟶ Y) (by rw [comp_zero, w]))
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ ?_) hmono hepi
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {W} ψ hψ => hS.gIsCokernel.desc (CokernelCofork.ofπ (pushout.inl f g ≫ ψ) (by
      rw [pushout.condition_assoc, hψ, comp_zero])))
    (fun {W} ψ hψ => ?_) (fun {W} ψ hψ m hm => ?_)
  · refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc_assoc]
      exact hS.gIsCokernel.fac _ WalkingParallelPair.one
    · rw [pushout.inr_desc_assoc, zero_comp]
      exact hψ.symm
  · apply Cofork.IsColimit.hom_ext hS.gIsCokernel
    have h := congrArg (pushout.inl f g ≫ ·) hm
    simp only [pushout.inl_desc_assoc] at h
    refine h.trans ?_
    exact (hS.gIsCokernel.fac (CokernelCofork.ofπ (pushout.inl f g ≫ ψ) (by
      rw [pushout.condition_assoc, hψ, comp_zero])) WalkingParallelPair.one).symm

end Pushout

/-! ### The unit of a right derived functor, read on cochain complexes -/

section Unit

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (B : C ⥤ D) [B.Additive] {RB : DerivedCategory C ⥤ DerivedCategory D}
  (u : B.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RB)

/-- The unit `u_K : B(K) ⟶ RB(K)` of a right derived functor of `B`, read on a cochain
complex `K`. -/
def unitQ (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      RB.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    DerivedCategory.Qh.map ((B.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
      u.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≫
        RB.map ((DerivedCategory.quotientCompQhIso C).hom.app K)

/-- The unit is natural: for `φ : K ⟶ L`, `Q(B(φ)) ≫ u_L = u_K ≫ RB(Q(φ))`. -/
lemma unitQ_naturality {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    DerivedCategory.Q.map ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ≫ unitQ B u L =
      unitQ B u K ≫ RB.map (DerivedCategory.Q.map φ) := by
  have h₁ := u.naturality ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ)
  have h₂ := (DerivedCategory.quotientCompQhIso D).inv.naturality
    ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)
  have h₃ := (DerivedCategory.quotientCompQhIso C).hom.naturality φ
  have h₄ := (B.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.naturality φ
  simp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂ h₃ h₄
  simp only [unitQ, Category.assoc]
  rw [reassoc_of% h₂, ← DerivedCategory.Qh.map_comp_assoc, h₄, DerivedCategory.Qh.map_comp_assoc,
    reassoc_of% h₁, ← RB.map_comp, ← RB.map_comp, h₃]

/-- If `u` is invertible on K-injective complexes, then `u_I : B(I) ⟶ RB(I)` is an isomorphism
for every K-injective complex `I`. -/
lemma isIso_unitQ (hu : ∀ I : CochainComplex C ℤ, I.IsKInjective →
      IsIso (u.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)))
    (I : CochainComplex C ℤ) [I.IsKInjective] : IsIso (unitQ B u I) := by
  have := hu I inferInstance
  dsimp only [unitQ]
  infer_instance

end Unit


/-! ### The row inclusion `B(K) ⊆ B(R(K))` and its cokernel -/

section Construction

open ColumnResolution

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (R : FunctorialResolution C) (B : C ⥤ D) [B.Additive] [PreservesFiniteLimits B]

/-- A cochain complex all of whose components are zero is zero. -/
lemma isZero_of_isZero_X {E : Type*} [Category E] [HasZeroMorphisms E]
    {K : CochainComplex E ℤ} (h : ∀ n, IsZero (K.X n)) : IsZero K := by
  rw [IsZero.iff_id_eq_zero]
  ext n
  exact (h n).eq_of_src _ _

/-- A morphism out of a zero object is a monomorphism. -/
lemma mono_of_isZero_src {E : Type*} [Category E] [HasZeroMorphisms E] {X Y : E} (f : X ⟶ Y)
    (h : IsZero X) : Mono f :=
  ⟨fun _ _ _ => h.eq_of_tgt _ _⟩

/-- The augmentation `B(X)[0] ⟶ B(R(X))` of a single object. -/
def colMap (X : C) :
    (HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (B.obj X) ⟶
      (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj (R.F.obj X) :=
  HomologicalComplex.mkHomFromSingle (B.map (R.aug₀ X)) (fun k hk => by
    obtain rfl : (1 : ℤ) = k := by simpa using hk
    change B.map (R.aug₀ X) ≫ B.map ((R.F.obj X).d 0 1) = 0
    rw [← B.map_comp, R.aug₀_comp_d, B.map_zero])

omit [PreservesFiniteLimits B] in
/-- In degree zero, `colMap R B X` is `B` applied to the augmentation `X ⟶ R(X)^0`, through the
identification of the degree-zero component of `B(X)[0]` with `B(X)`. -/
lemma colMap_f_zero (X : C) :
    (colMap R B X).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (B.obj X)).hom ≫
        B.map (R.aug₀ X) :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- Every component of the augmentation `B(X)[0] ⟶ B(R(X))` is a monomorphism. -/
instance (X : C) (q : ℤ) : Mono ((colMap R B X).f q) := by
  by_cases hq : q = 0
  · subst hq
    rw [colMap_f_zero]
    infer_instance
  · exact mono_of_isZero_src _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

/-- The augmentation `B(X)[0] ⟶ B(R(X))` is a monomorphism. -/
instance (X : C) : Mono (colMap R B X) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstance)

omit [PreservesFiniteLimits B] in
/-- The augmentation `B(X)[0] ⟶ B(R(X))` is natural in `X`. -/
lemma colMap_naturality {X Y : C} (g : X ⟶ Y) :
    colMap R B X ≫ (B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map g) =
      (HomologicalComplex.single D (ComplexShape.up ℤ) 0).map (B.map g) ≫ colMap R B Y := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, colMap_f_zero, colMap_f_zero,
    HomologicalComplex.single_map_f_self]
  simp only [Functor.mapHomologicalComplex_map_f, Category.assoc, Iso.inv_hom_id_assoc,
    ← B.map_comp, R.aug₀_naturality]

/-- **`B` is left exact, so `H^0(B(R(X))) = B(X)`**: the augmentation induces an isomorphism in
degree-zero cohomology. -/
lemma isIso_homologyMap_colMap_zero (X : C) : IsIso (homologyMap (colMap R B X) 0) := by
  set A := (HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (B.obj X)
  set Bc := (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj (R.F.obj X)
  have hA₁ : IsIso (A.iCycles 0) := A.isIso_iCycles 0 1 (by simp)
    (IsZero.eq_of_tgt (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)) _ _)
  have hπA : IsIso (A.homologyπ 0) := A.isIso_homologyπ (-1) 0 (by simp)
    (IsZero.eq_of_src (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)) _ _)
  have hπB : IsIso (Bc.homologyπ 0) := Bc.isIso_homologyπ (-1) 0 (by simp)
    (IsZero.eq_of_src (B.map_isZero
      (CochainComplex.isZero_of_isStrictlyGE (R.F.obj X) 0 (-1) (by omega))) _ _)
  have hφ : IsIso ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (B.obj X)).inv ≫
      inv (A.iCycles 0) ≫ cyclesMap (colMap R B X) 0) :=
    isIso_of_isLimit_kernelFork (ι₁ := B.map (R.aug₀ X))
      (w₁ := by rw [← B.map_comp, R.aug₀_comp_d, B.map_zero])
      (KernelFork.mapIsLimit _ (R.isLimitAug₀ X) B)
      (Bc.cyclesIsKernel 0 1 (by simp)) _ (by
        rw [Category.assoc, Category.assoc, cyclesMap_i, IsIso.inv_hom_id_assoc, colMap_f_zero,
          Iso.inv_hom_id_assoc])
  have hZ : IsIso (cyclesMap (colMap R B X) 0) := by
    have h' : IsIso (inv (A.iCycles 0) ≫ cyclesMap (colMap R B X) 0) :=
      IsIso.of_isIso_comp_left
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (B.obj X)).inv _
    exact IsIso.of_isIso_comp_left (inv (A.iCycles 0)) _
  have : homologyMap (colMap R B X) 0 =
      inv (A.homologyπ 0) ≫ cyclesMap (colMap R B X) 0 ≫ Bc.homologyπ 0 := by
    rw [← homologyπ_naturality, IsIso.inv_hom_id_assoc]
  rw [this]
  infer_instance

variable (K : CochainComplex C ℤ) [K.IsStrictlyGE 0]

/-- The row `B(K)`, placed in second degree zero. -/
abbrev row : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  singleRowZero ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

/-- The inclusion of the row `B(K)` into the double complex `B(R(K))`. -/
def rowMap : row B K ⟶ R.mapBicomplex K B where
  f p := colMap R B (K.X p)
  comm' p p' _ := colMap_naturality R B (K.d p p')

omit [PreservesFiniteLimits B] in
/-- The row `B(K)` vanishes in negative first degree. -/
lemma isZero_row_X (p : ℤ) (hp : p < 0) : IsZero ((row B K).X p) :=
  Functor.map_isZero (HomologicalComplex.single D (ComplexShape.up ℤ) 0)
    (B.map_isZero (K.isZero_of_isStrictlyGE 0 p hp))

omit [PreservesFiniteLimits B] [K.IsStrictlyGE 0] in
/-- The row `B(K)` vanishes outside second degree zero. -/
lemma isZero_row_X_X (p q : ℤ) (hq : q ≠ 0) : IsZero (((row B K).X p).X q) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hq

/-- The row `B(K)` has a total complex. -/
instance : (row B K).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_bounded _ 0 (fun p q hq => isZero_row_X_X B K p q (by omega)) (isZero_row_X B K)

omit [PreservesFiniteLimits B] [K.IsStrictlyGE 0] in
/-- A component of the cokernel of the row inclusion vanishes wherever the corresponding
component of `B(R(K))` does. -/
lemma isZero_cokernel_rowMap_X_X (p q : ℤ) (h : IsZero (((R.mapBicomplex K B).X p).X q)) :
    IsZero (((cokernel (rowMap R B K)).X p).X q) :=
  have := epi_of_isColimit_cofork (isColimit_cokernelCofork_f_f (rowMap R B K) p q)
  IsZero.of_epi (((cokernel.π (rowMap R B K)).f p).f q) h

omit [PreservesFiniteLimits B] in
/-- The cokernel of the row inclusion vanishes in negative first degree. -/
lemma isZero_cokernel_rowMap_X (p : ℤ) (hp : p < 0) :
    IsZero ((cokernel (rowMap R B K)).X p) :=
  isZero_of_isZero_X (fun q => isZero_cokernel_rowMap_X_X R B K p q
    (Functor.map_isZero (HomologicalComplex.eval D (ComplexShape.up ℤ) q)
      (R.isZero_mapBicomplex_X K B p hp)))

omit [PreservesFiniteLimits B] [K.IsStrictlyGE 0] in
/-- The cokernel of the row inclusion vanishes in negative second degree. -/
lemma isZero_cokernel_rowMap_X_X_of_neg (p q : ℤ) (hq : q < 0) :
    IsZero (((cokernel (rowMap R B K)).X p).X q) :=
  isZero_cokernel_rowMap_X_X R B K p q (R.isZero_mapBicomplex_X_X K B p q hq)

/-- The cokernel of the row inclusion has a total complex. -/
instance : (cokernel (rowMap R B K)).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_bounded _ 0 (isZero_cokernel_rowMap_X_X_of_neg R B K)
    (isZero_cokernel_rowMap_X R B K)

/-- The inclusion `B(K) ⟶ Tot(B(R(K)))` of the row. -/
def incl : ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K : CochainComplex D ℤ) ⟶
    ((R.mapBicomplex K B).total (ComplexShape.up ℤ) : CochainComplex D ℤ) :=
  totalSingleRowZeroUnit _ ≫ HomologicalComplex₂.total.map (rowMap R B K) (ComplexShape.up ℤ)

omit [PreservesFiniteLimits B] in
/-- Read through `Tot(B(R(K))) ≅ B(Tot(R(K)))`, the inclusion of the row is `B` applied to the
comparison `K ⟶ Tot(R(K))`. -/
lemma incl_comp_mapTotalIso :
    incl R B K ≫ (R.mapTotalIso K B).hom =
      (B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.totalComparison K) := by
  ext n
  rw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    FunctorialResolution.totalComparison_f, B.map_comp]
  dsimp only [incl, FunctorialResolution.mapTotalIso]
  rw [HomologicalComplex₂.TotalMap.totalIsoOfFinite_hom_eq_totalMap, HomologicalComplex.comp_f]
  show ((totalSingleRowZeroUnit _).f n ≫ _) ≫
    HomologicalComplex₂.TotalMap.totalMapf B (R.bicomplex K) n = _
  simp only [totalSingleRowZeroUnit, Category.assoc, HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.TotalMap.ι_totalMapf]
  show _ ≫ (colMap R B (K.X n)).f 0 ≫ _ = _
  rw [colMap_f_zero, Category.assoc]
  exact Iso.inv_hom_id_assoc _ _

/-- Every component of the inclusion `B(K) ⟶ Tot(B(R(K)))` is a monomorphism. -/
instance (n : ℤ) : Mono ((incl R B K).f n) := by
  have : Mono ((incl R B K).f n ≫ ((R.mapTotalIso K B).hom).f n) := by
    rw [← HomologicalComplex.comp_f, incl_comp_mapTotalIso]
    dsimp
    infer_instance
  exact mono_of_mono _ (((R.mapTotalIso K B).hom).f n)

/-- The inclusion `B(K) ⟶ Tot(B(R(K)))` is a monomorphism. -/
instance : Mono (incl R B K) := HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstance)

/-- The projection `Tot(B(R(K))) ⟶ Tot(coker)` onto the total complex of the cokernel. -/
abbrev proj : (R.mapBicomplex K B).total (ComplexShape.up ℤ) ⟶
    (cokernel (rowMap R B K)).total (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.map (cokernel.π (rowMap R B K)) (ComplexShape.up ℤ)

/-- Precomposing with an isomorphism does not change a cokernel. -/
def isColimitCokernelCoforkPrecomp {E : Type*} [Category E] [Preadditive E] {X' X Y Z : E}
    (e : X' ⟶ X) [IsIso e] (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : IsColimit (CokernelCofork.ofπ (f := f) g w)) :
    IsColimit (CokernelCofork.ofπ (f := e ≫ f) g (by rw [Category.assoc, w, comp_zero])) :=
  have hw : ∀ {W : E} (φ : Y ⟶ W), (e ≫ f) ≫ φ = 0 → f ≫ φ = 0 := fun φ hφ => by
    rw [← cancel_epi e, comp_zero, ← Category.assoc, hφ]
  CokernelCofork.IsColimit.ofπ _ _
    (fun φ hφ => h.desc (CokernelCofork.ofπ φ (hw φ hφ)))
    (fun φ hφ => h.fac (CokernelCofork.ofπ φ (hw φ hφ)) WalkingParallelPair.one)
    (fun φ hφ m hm => Cofork.IsColimit.hom_ext h
      (hm.trans (h.fac (CokernelCofork.ofπ φ (hw φ hφ)) WalkingParallelPair.one).symm))

/-- **The short exact sequence `0 ⟶ B(K) ⟶ Tot(B(R(K))) ⟶ Tot(coker) ⟶ 0`.** -/
abbrev ses : ShortComplex (CochainComplex D ℤ) :=
  ShortComplex.mk (incl R B K) (proj R B K) (by
    rw [incl, Category.assoc, ← HomologicalComplex₂.total.map_comp, cokernel.condition,
      HomologicalComplex₂.total_map_zero, comp_zero])

/-- The sequence `0 ⟶ B(K) ⟶ Tot(B(R(K))) ⟶ Tot(coker) ⟶ 0` is short exact. -/
lemma ses_shortExact : (ses R B K).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
  have hc := total_isColimit_cokernelCofork (rowMap R B K) n
  have := isIso_totalSingleRowZeroUnit_f ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n
  have hc' := isColimitCokernelCoforkPrecomp
    ((totalSingleRowZeroUnit ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).f n) _ _ _ hc
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hc')
    (inferInstanceAs (Mono ((incl R B K).f n))) (epi_of_isColimit_cofork hc)

end Construction

/-! ### Naturality, and the column computation -/

section Naturality

open ColumnResolution

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (R : FunctorialResolution C) (B : C ⥤ D) [B.Additive] [PreservesFiniteLimits B]
  {K M : CochainComplex C ℤ} [K.IsStrictlyGE 0] [M.IsStrictlyGE 0] (ρ : K ⟶ M)

/-- The morphism `B(R(ρ)) : B(R(K)) ⟶ B(R(M))` of double complexes. -/
abbrev mapBicomplexMap : R.mapBicomplex K B ⟶ R.mapBicomplex M B :=
  ((B.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((R.F.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ)

/-- The morphism of rows `B(ρ)`. -/
abbrev rowMapMap : row B K ⟶ row B M :=
  ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).mapHomologicalComplex
    (ComplexShape.up ℤ)).map ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ)

omit [PreservesFiniteLimits B] [K.IsStrictlyGE 0] [M.IsStrictlyGE 0] in
/-- The row inclusion is natural: `rowMap R B K ≫ B(R(ρ)) = B(ρ) ≫ rowMap R B M`. -/
lemma rowMap_naturality :
    rowMap R B K ≫ mapBicomplexMap R B ρ = rowMapMap B ρ ≫ rowMap R B M :=
  HomologicalComplex.hom_ext _ _ (fun p => colMap_naturality R B (ρ.f p))

/-- The induced morphism of cokernels. -/
abbrev cokernelMap : cokernel (rowMap R B K) ⟶ cokernel (rowMap R B M) :=
  cokernel.map _ _ (rowMapMap B ρ) (mapBicomplexMap R B ρ) (rowMap_naturality R B ρ)

/-- The morphism of short exact sequences induced by `ρ`. -/
def sesMap : ses R B K ⟶ ses R B M where
  τ₁ := (B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ
  τ₂ := HomologicalComplex₂.total.map (mapBicomplexMap R B ρ) (ComplexShape.up ℤ)
  τ₃ := HomologicalComplex₂.total.map (cokernelMap R B ρ) (ComplexShape.up ℤ)
  comm₁₂ := by
    have h :=
      totalSingleRowZeroUnit_naturality ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ)
    dsimp only [ses, incl]
    rw [Category.assoc, ← HomologicalComplex₂.total.map_comp, rowMap_naturality,
      HomologicalComplex₂.total.map_comp, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) h.symm
  comm₂₃ := by
    dsimp only [ses, proj]
    rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
    congr 1
    simp

/-- Column `p` of the row inclusion, as a short exact sequence of cochain complexes. -/
def colSes (L : CochainComplex C ℤ) [L.IsStrictlyGE 0] (p : ℤ) :
    ShortComplex (CochainComplex D ℤ) :=
  ShortComplex.mk ((rowMap R B L).f p) ((cokernel.π (rowMap R B L)).f p) (by
    rw [← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f])

/-- Column `p` of the row inclusion, `0 ⟶ B(L^p)[0] ⟶ B(R(L^p)) ⟶ coker ⟶ 0`, is short exact. -/
lemma colSes_shortExact (L : CochainComplex C ℤ) [L.IsStrictlyGE 0] (p : ℤ) :
    (colSes R B L p).ShortExact := by
  have hc : IsColimit (CokernelCofork.ofπ (f := (rowMap R B L).f p)
      ((cokernel.π (rowMap R B L)).f p) (colSes R B L p).zero) :=
    isColimitOfHasCokernelOfPreservesColimit (HomologicalComplex.eval _ _ p) (rowMap R B L)
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hc)
    (inferInstanceAs (Mono (colMap R B (L.X p)))) (epi_of_isColimit_cofork hc)

/-- The morphism of column short exact sequences induced by `ρ`. -/
def colSesMap (p : ℤ) : colSes R B K p ⟶ colSes R B M p where
  τ₁ := (rowMapMap B ρ).f p
  τ₂ := (mapBicomplexMap R B ρ).f p
  τ₃ := (cokernelMap R B ρ).f p
  comm₁₂ := by
    dsimp only [colSes]
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, rowMap_naturality]
  comm₂₃ := by
    dsimp only [colSes]
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    simp

section Column

variable (L : CochainComplex C ℤ) [L.IsStrictlyGE 0] (p : ℤ)

omit [PreservesFiniteLimits B] in
/-- The single complex `B(L^p)[0]` has zero cohomology in every nonzero degree. -/
lemma isZero_colSes_X₁_homology (q : ℤ) (hq : q ≠ 0) :
    IsZero ((colSes R B L p).X₁.homology q) :=
  (HomologicalComplex.exactAt_single_obj _ _ _ _ hq).isZero_homology

/-- Column `p` of the cokernel of the row inclusion has zero cohomology in every degree `q ≤ 0`. -/
lemma isZero_colSes_X₃_homology (q : ℤ) (hq : q ≤ 0) :
    IsZero ((colSes R B L p).X₃.homology q) := by
  rcases lt_or_eq_of_le hq with hq | rfl
  · exact isZero_homology_of_isZero_X q (isZero_cokernel_rowMap_X_X_of_neg R B L p q hq)
  · have hS := colSes_shortExact R B L p
    have hf : IsIso (homologyMap (colSes R B L p).f 0) := isIso_homologyMap_colMap_zero R B (L.X p)
    have hepi : Epi (homologyMap (colSes R B L p).g 0) :=
      (hS.homology_exact₃ 0 1 (by simp)).epi_f
        ((isZero_colSes_X₁_homology R B L p 1 (by omega)).eq_of_tgt _ _)
    have hzero : homologyMap (colSes R B L p).g 0 = 0 := by
      rw [← cancel_epi (homologyMap (colSes R B L p).f 0), comp_zero, ← homologyMap_comp,
        (colSes R B L p).zero, homologyMap_zero]
    rw [IsZero.iff_id_eq_zero, ← cancel_epi (homologyMap (colSes R B L p).g 0)]
    simp [hzero]

/-- In every positive degree, the projection of `B(R(L^p))` onto column `p` of the cokernel of
the row inclusion induces an isomorphism in cohomology. -/
lemma isIso_colSes_g_homology (q : ℤ) (hq : 0 < q) :
    IsIso (homologyMap (colSes R B L p).g q) := by
  have hS := colSes_shortExact R B L p
  have : Mono (homologyMap (colSes R B L p).g q) :=
    (hS.homology_exact₂ q).mono_g
      ((isZero_colSes_X₁_homology R B L p q (by omega)).eq_of_src _ _)
  have : Epi (homologyMap (colSes R B L p).g q) :=
    (hS.homology_exact₃ q (q + 1) (by simp)).epi_f
      ((isZero_colSes_X₁_homology R B L p (q + 1) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Column

variable {R B ρ} in
/-- **The column computation.** If `ρ` induces isomorphisms on the cohomology of
`B(R(K^p)) ⟶ B(R(M^p))` in positive degrees, the morphism of cokernels of the row inclusions is
a quasi-isomorphism in every column. -/
lemma quasiIso_cokernelMap_f
    (hρ : ∀ (p q : ℤ), 0 < q → IsIso (homologyMap
      ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map (ρ.f p))) q)) (p : ℤ) :
    QuasiIso ((cokernelMap R B ρ).f p) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hq : q ≤ 0
  · exact isIso_of_isZero _ (isZero_colSes_X₃_homology R B K p q hq)
      (isZero_colSes_X₃_homology R B M p q hq)
  · have h₁ := isIso_colSes_g_homology R B K p q (by omega)
    have h₂ := isIso_colSes_g_homology R B M p q (by omega)
    have h₃ := hρ p q (by omega)
    have hc := congrArg (fun φ => homologyMap φ q) (colSesMap R B ρ p).comm₂₃
    simp only [homologyMap_comp] at hc
    have e : IsIso (homologyMap (colSes R B K p).g q ≫
        homologyMap (colSesMap R B ρ p).τ₃ q) := by
      rw [← hc]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₃ h₂
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₁ e

variable {R B ρ} in
/-- The morphism of total complexes of cokernels is a quasi-isomorphism ([Stacks, Tag 0133]). -/
lemma quasiIso_total_cokernelMap
    (hρ : ∀ (p q : ℤ), 0 < q → IsIso (homologyMap
      ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map (ρ.f p))) q)) :
    QuasiIso (HomologicalComplex₂.total.map (cokernelMap R B ρ) (ComplexShape.up ℤ)) :=
  quasiIso_total_map _ 0 (isZero_cokernel_rowMap_X_X_of_neg R B K)
    (isZero_cokernel_rowMap_X R B K) (isZero_cokernel_rowMap_X_X_of_neg R B M)
    (isZero_cokernel_rowMap_X R B M) (quasiIso_cokernelMap_f hρ)

/-! ### Pushing the row inclusion out along `B(ρ)` -/

omit [PreservesFiniteLimits B] in
/-- The row inclusions commute with `B(ρ)` and with `Tot(B(R(ρ)))`. -/
lemma incl_comm : incl R B K ≫ (sesMap R B ρ).τ₂ =
    (B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ ≫ incl R B M :=
  (sesMap R B ρ).comm₁₂.symm

/-- The comparison `P ⟶ Tot(B(R(M)))` out of the pushout. -/
def pushoutComparison : pushout (incl R B K) ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) ⟶
    (R.mapBicomplex M B).total (ComplexShape.up ℤ) :=
  pushout.desc (f := incl R B K) (g := (B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) _ _
    (incl_comm R B ρ)

omit [PreservesFiniteLimits B] in
/-- The inclusion `B(K) ⟶ Tot(B(R(K)))` followed by the projection onto `Tot(coker)` is zero. -/
lemma incl_proj : incl R B K ≫ proj R B K = 0 := (ses R B K).zero

/-- The short exact sequence `0 ⟶ B(M) ⟶ P ⟶ Tot(coker) ⟶ 0` of the pushout. -/
abbrev pushoutSes : ShortComplex (CochainComplex D ℤ) :=
  ShortComplex.mk (pushout.inr (incl R B K) ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ))
    (pushout.desc (proj R B K) 0 (by rw [comp_zero, incl_proj R B (K := K)]))
    (pushout.inr_desc _ _ _)

omit [M.IsStrictlyGE 0] in
/-- The sequence `0 ⟶ B(M) ⟶ P ⟶ Tot(coker) ⟶ 0` of the pushout is short exact. -/
lemma pushoutSes_shortExact : (pushoutSes R B ρ).ShortExact :=
  shortExact_pushout_inr _ _ (proj R B K) (incl_proj R B (K := K)) (ses_shortExact R B K)

omit [PreservesFiniteLimits B] in
/-- On `Tot(B(R(K)))`, the comparison `P ⟶ Tot(B(R(M)))` restricts to `Tot(B(R(ρ)))`. -/
@[reassoc]
lemma inl_pushoutComparison :
    pushout.inl (incl R B K) ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) ≫
      pushoutComparison R B ρ = (sesMap R B ρ).τ₂ := pushout.inl_desc _ _ _

omit [PreservesFiniteLimits B] in
/-- On `B(M)`, the comparison `P ⟶ Tot(B(R(M)))` restricts to the inclusion of the row. -/
@[reassoc]
lemma inr_pushoutComparison :
    pushout.inr (incl R B K) ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) ≫
      pushoutComparison R B ρ = incl R B M := pushout.inr_desc _ _ _

omit [PreservesFiniteLimits B] [M.IsStrictlyGE 0] in
/-- On `Tot(B(R(K)))`, the projection `P ⟶ Tot(coker)` restricts to `proj R B K`. -/
@[reassoc]
lemma inl_pushoutSes_g :
    pushout.inl (incl R B K) ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) ≫
      (pushoutSes R B ρ).g = proj R B K := pushout.inl_desc _ _ _

omit [PreservesFiniteLimits B] [M.IsStrictlyGE 0] in
/-- The projection `P ⟶ Tot(coker)` vanishes on `B(M)`. -/
@[reassoc]
lemma inr_pushoutSes_g :
    pushout.inr (incl R B K) ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) ≫
      (pushoutSes R B ρ).g = 0 := pushout.inr_desc _ _ _

/-- The morphism from the short exact sequence of the pushout to that of `M`. -/
def pushoutSesMap : pushoutSes R B ρ ⟶ ses R B M where
  τ₁ := 𝟙 _
  τ₂ := pushoutComparison R B ρ
  τ₃ := (sesMap R B ρ).τ₃
  comm₁₂ := (Category.id_comp _).trans (inr_pushoutComparison R B ρ).symm
  comm₂₃ := by
    refine pushout.hom_ext ?_ ?_
    · exact (inl_pushoutComparison_assoc R B ρ _).trans ((sesMap R B ρ).comm₂₃.trans
        (inl_pushoutSes_g_assoc R B ρ _).symm)
    · exact (inr_pushoutComparison_assoc R B ρ _).trans ((ses R B M).zero.trans
        ((inr_pushoutSes_g_assoc R B ρ _).trans zero_comp).symm)

variable {R B ρ} in
/-- **The comparison out of the pushout is a quasi-isomorphism.** -/
lemma quasiIso_pushoutComparison
    (hρ : ∀ (p q : ℤ), 0 < q → IsIso (homologyMap
      ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map (ρ.f p))) q)) :
    QuasiIso (pushoutComparison R B ρ) := by
  have : QuasiIso (pushoutSesMap R B ρ).τ₃ := quasiIso_total_cokernelMap hρ
  have : QuasiIso (pushoutSesMap R B ρ).τ₁ :=
    inferInstanceAs (QuasiIso (𝟙 ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)))
  exact quasiIso_τ₂ (pushoutSesMap R B ρ) (pushoutSes_shortExact R B ρ) (ses_shortExact R B M)


end Naturality

/-! ### The homotopy cartesian square -/

section Main

open ColumnResolution

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (B : C ⥤ D) [B.Additive] [PreservesFiniteLimits B]
  {RB : DerivedCategory C ⥤ DerivedCategory D}
  (u : B.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RB)
  (hu : ∀ I : CochainComplex C ℤ, I.IsKInjective →
    IsIso (u.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)))
  (R : FunctorialResolution C)

/-- The localization functor `Q` to the derived category preserves binary biproducts. -/
instance : PreservesBinaryBiproducts (DerivedCategory.Q (C := D)) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

omit [HasDerivedCategory C] in
/-- Through `Q(X ⊞ Y) ≅ Q(X) ⊞ Q(Y)`, the image under `Q` of the morphism `(a, b) : W ⟶ X ⊞ Y`
is `(Q(a), Q(b))`. -/
lemma Q_map_lift_comp_mapBiprod_hom {W X Y : CochainComplex D ℤ} (a : W ⟶ X) (b : W ⟶ Y) :
    DerivedCategory.Q.map (biprod.lift a b) ≫ (DerivedCategory.Q.mapBiprod X Y).hom =
      biprod.lift (DerivedCategory.Q.map a) (DerivedCategory.Q.map b) := by
  apply biprod.hom_ext
  · rw [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, ← Functor.map_comp,
      biprod.lift_fst, biprod.lift_fst]
  · rw [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd, ← Functor.map_comp,
      biprod.lift_snd, biprod.lift_snd]

omit [HasDerivedCategory C] in
/-- Through `Q(X ⊞ Y) ≅ Q(X) ⊞ Q(Y)`, the image under `Q` of the morphism `(a, b) : X ⊞ Y ⟶ W`
is `(Q(a), Q(b))`. -/
lemma Q_map_desc {W X Y : CochainComplex D ℤ} (a : X ⟶ W) (b : Y ⟶ W) :
    DerivedCategory.Q.map (biprod.desc a b) = (DerivedCategory.Q.mapBiprod X Y).hom ≫
      biprod.desc (DerivedCategory.Q.map a) (DerivedCategory.Q.map b) := by
  rw [← Iso.inv_comp_eq, Functor.mapBiprod_inv]
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, ← Functor.map_comp, biprod.inl_desc, biprod.inl_desc]
  · rw [biprod.inr_desc_assoc, ← Functor.map_comp, biprod.inr_desc, biprod.inr_desc]

/-- The image in the derived category of a quasi-isomorphism is an isomorphism. -/
instance {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    IsIso (DerivedCategory.Q.map f) := by
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  infer_instance

/-- **`Tot(B(R(K)))` computes `RB(K)`.** -/
def totalIso (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] :
    DerivedCategory.Q.obj ((R.mapBicomplex K B).total (ComplexShape.up ℤ)) ≅
      RB.obj (DerivedCategory.Q.obj K) :=
  have := isIso_unitQ B u hu (R.total K)
  DerivedCategory.Q.mapIso (R.mapTotalIso K B) ≪≫ asIso (unitQ B u (R.total K)) ≪≫
    (RB.mapIso (asIso (DerivedCategory.Q.map (R.totalComparison K)))).symm

omit [PreservesFiniteLimits B] in
/-- The isomorphism `totalIso` is the composite of `Tot(B(R(K))) ≅ B(Tot(R(K)))`, the unit
`u_{Tot(R(K))}`, and the inverse of `RB` of the comparison `K ⟶ Tot(R(K))`. -/
lemma totalIso_hom (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] :
    (totalIso B u hu R K).hom = DerivedCategory.Q.map (R.mapTotalIso K B).hom ≫
      unitQ B u (R.total K) ≫ RB.map (inv (DerivedCategory.Q.map (R.totalComparison K))) := by
  simp [totalIso]

omit [PreservesFiniteLimits B] in
/-- Through `totalIso`, the inclusion of the row is the unit `u_K`. -/
lemma Q_map_incl_comp_totalIso_hom (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] :
    DerivedCategory.Q.map (incl R B K) ≫ (totalIso B u hu R K).hom = unitQ B u K := by
  rw [totalIso_hom, ← DerivedCategory.Q.map_comp_assoc, incl_comp_mapTotalIso,
    reassoc_of% unitQ_naturality, ← RB.map_comp, IsIso.hom_inv_id, RB.map_id,
    Category.comp_id]

omit [PreservesFiniteLimits B] in
/-- Through `totalIso`, the morphism of total complexes induced by `ρ` is `RB(ρ)`. -/
lemma Q_map_total_comp_totalIso_hom {K M : CochainComplex C ℤ} [K.IsStrictlyGE 0]
    [M.IsStrictlyGE 0] (ρ : K ⟶ M) :
    DerivedCategory.Q.map (HomologicalComplex₂.total.map (mapBicomplexMap R B ρ)
        (ComplexShape.up ℤ)) ≫ (totalIso B u hu R M).hom =
      (totalIso B u hu R K).hom ≫ RB.map (DerivedCategory.Q.map ρ) := by
  have h₁ : HomologicalComplex₂.total.map (mapBicomplexMap R B ρ) (ComplexShape.up ℤ) ≫
      (R.mapTotalIso M B).hom = (R.mapTotalIso K B).hom ≫
        (B.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex₂.total.map ((R.F.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ)
            (ComplexShape.up ℤ)) :=
    HomologicalComplex₂.TotalMap.totalMap_naturality B _ _
  have h₂ : DerivedCategory.Q.map (HomologicalComplex₂.total.map
        ((R.F.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) (ComplexShape.up ℤ)) ≫
      inv (DerivedCategory.Q.map (R.totalComparison M)) =
      inv (DerivedCategory.Q.map (R.totalComparison K)) ≫ DerivedCategory.Q.map ρ := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_comp, R.totalComparison_naturality]
  rw [totalIso_hom, totalIso_hom, ← DerivedCategory.Q.map_comp_assoc, h₁,
    DerivedCategory.Q.map_comp_assoc, reassoc_of% unitQ_naturality, ← RB.map_comp, h₂,
    RB.map_comp]
  simp only [Category.assoc]

/-- The pasted version of `exists_distTriang_of_resolution`, for any bicartesian square
below `B(ρ)`. -/
private theorem exists_distTriang_of_isPushout_of_resolution_aux
    (hu : ∀ I : CochainComplex C ℤ, I.IsKInjective →
      IsIso (u.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)))
    {K M : CochainComplex C ℤ} [K.IsStrictlyGE 0] [M.IsStrictlyGE 0] (ρ : K ⟶ M)
    (hρ : ∀ (p q : ℤ), 0 < q → IsIso (homologyMap
      ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map (ρ.f p))) q))
    {A N : CochainComplex D ℤ} (α : A ⟶ (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (β : A ⟶ N) (γ : N ⟶ (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
    (hsq : IsPushout α β ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) γ)
    (hmono : Mono (biprod.lift α (-β))) :
    ∃ δ : RB.obj (DerivedCategory.Q.obj M) ⟶ (DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk
          (biprod.lift (DerivedCategory.Q.map α ≫ unitQ B u K) (DerivedCategory.Q.map β))
          (biprod.desc (RB.map (DerivedCategory.Q.map ρ))
            (-(DerivedCategory.Q.map γ ≫ unitQ B u M))) δ ∈
        distTriang (DerivedCategory D) := by
  have hout := hsq.paste_horiz
    (IsPushout.of_hasPushout (incl R B K) ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ))
  have hm : Mono (biprod.lift (α ≫ incl R B K) (-β)) := by
    rw [show biprod.lift (α ≫ incl R B K) (-β) =
      biprod.lift α (-β) ≫ biprod.map (incl R B K) (𝟙 N) by apply biprod.hom_ext <;> simp]
    infer_instance
  have hP : hout.toCommSq.shortComplex.ShortExact :=
    ShortComplex.ShortExact.mk' hout.exact_shortComplex hm hout.epi_shortComplex_g
  have hc := quasiIso_pushoutComparison hρ
  have hT := DerivedCategory.triangleOfSES_distinguished hP
  let n : DerivedCategory.Q.obj N ≅ DerivedCategory.Q.obj N := { hom := -𝟙 _, inv := -𝟙 _ }
  let e₂ := DerivedCategory.Q.mapBiprod ((R.mapBicomplex K B).total (ComplexShape.up ℤ)) N ≪≫
    biprod.mapIso (totalIso B u hu R K) n
  let e₃ := asIso (DerivedCategory.Q.map (pushoutComparison R B ρ)) ≪≫ totalIso B u hu R M
  refine ⟨e₃.inv ≫ (DerivedCategory.triangleOfSES hP).mor₃,
    Pretriangulated.isomorphic_distinguished _ hT _
      (Pretriangulated.Triangle.isoMk (DerivedCategory.triangleOfSES hP)
        (Pretriangulated.Triangle.mk
          (biprod.lift (DerivedCategory.Q.map α ≫ unitQ B u K) (DerivedCategory.Q.map β))
          (biprod.desc (RB.map (DerivedCategory.Q.map ρ))
            (-(DerivedCategory.Q.map γ ≫ unitQ B u M)))
          (e₃.inv ≫ (DerivedCategory.triangleOfSES hP).mor₃))
        (Iso.refl _) e₂ e₃ ?_ ?_ ?_).symm⟩
  · show DerivedCategory.Q.map (biprod.lift (α ≫ incl R B K) (-β)) ≫
        ((DerivedCategory.Q.mapBiprod _ _).hom ≫ biprod.map (totalIso B u hu R K).hom n.hom) =
      𝟙 _ ≫ biprod.lift (DerivedCategory.Q.map α ≫ unitQ B u K) (DerivedCategory.Q.map β)
    rw [← Category.assoc, Q_map_lift_comp_mapBiprod_hom, Category.id_comp]
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst,
        DerivedCategory.Q.map_comp, Category.assoc, Q_map_incl_comp_totalIso_hom]
    · rw [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]
      simp [n]
  · show DerivedCategory.Q.map (biprod.desc (pushout.inl (incl R B K)
          ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ))
          (γ ≫ pushout.inr (incl R B K) ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ))) ≫
        (DerivedCategory.Q.map (pushoutComparison R B ρ) ≫ (totalIso B u hu R M).hom) =
      ((DerivedCategory.Q.mapBiprod _ _).hom ≫ biprod.map (totalIso B u hu R K).hom n.hom) ≫
        biprod.desc (RB.map (DerivedCategory.Q.map ρ)) (-(DerivedCategory.Q.map γ ≫ unitQ B u M))
    rw [Q_map_desc, Category.assoc, Category.assoc]
    congr 1
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc,
        ← DerivedCategory.Q.map_comp_assoc, inl_pushoutComparison]
      exact Q_map_total_comp_totalIso_hom B u hu R ρ
    · rw [biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc,
        ← DerivedCategory.Q.map_comp_assoc, Category.assoc, inr_pushoutComparison,
        DerivedCategory.Q.map_comp_assoc, Q_map_incl_comp_totalIso_hom]
      simp [n]
  · dsimp only [Pretriangulated.Triangle.mk_mor₃]
    have h₁ : (shiftFunctor (DerivedCategory D) (1 : ℤ)).map
        (𝟙 (DerivedCategory.triangleOfSES hP).obj₁) = 𝟙 _ := (shiftFunctor _ _).map_id _
    exact (congrArg (fun x => (DerivedCategory.triangleOfSES hP).mor₃ ≫ x) h₁).trans
      ((Category.comp_id _).trans (Iso.hom_inv_id_assoc e₃ _).symm)

variable {B u hu R} in
include hu in
/-- **The derived unit square is homotopy cartesian**, given a functorial resolution `R` and the
cohomological hypothesis read on it. -/
theorem exists_distTriang_of_resolution {K M : CochainComplex C ℤ} [K.IsStrictlyGE 0]
    [M.IsStrictlyGE 0] (ρ : K ⟶ M)
    (hρ : ∀ (p q : ℤ), 0 < q → IsIso (homologyMap
      ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map (ρ.f p))) q)) :
    ∃ δ : RB.obj (DerivedCategory.Q.obj M) ⟶
        (DerivedCategory.Q.obj ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk
          (biprod.lift (unitQ B u K)
            (DerivedCategory.Q.map ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ)))
          (biprod.desc (RB.map (DerivedCategory.Q.map ρ)) (-unitQ B u M)) δ ∈
        distTriang (DerivedCategory D) := by
  have hsq : IsPushout (𝟙 _) ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ)
      ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) (𝟙 _) :=
    IsPushout.of_horiz_isIso ⟨by simp⟩
  simpa using exists_distTriang_of_isPushout_of_resolution_aux B u R hu ρ hρ _ _ _ hsq
    (mono_of_mono_fac
      (biprod.lift_fst (𝟙 _) (-(B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ)))

variable {B u hu R} in
include hu in
/-- **The derived unit square pasted with a bicartesian square is homotopy cartesian**, given a
functorial resolution `R`: if `A ⟶ B(K)`, `A ⟶ N`, `B(ρ)`, `N ⟶ B(M)` form a bicartesian square of
complexes (a pushout square with `A ⟶ B(K) ⊞ N` a monomorphism), then there is a distinguished
triangle `A ⟶ RB(K) ⊞ N ⟶ RB(M) ⟶ A[1]` with first map `(u_K ∘ α, β)` and second map
`(RB(ρ), -u_M ∘ γ)`. For `A = B(K)`, `N = B(M)` this is `exists_distTriang_of_resolution`. -/
theorem exists_distTriang_of_isPushout_of_resolution {K M : CochainComplex C ℤ} [K.IsStrictlyGE 0]
    [M.IsStrictlyGE 0] (ρ : K ⟶ M)
    (hρ : ∀ (p q : ℤ), 0 < q → IsIso (homologyMap
      ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map (ρ.f p))) q))
    {A N : CochainComplex D ℤ} (α : A ⟶ (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (β : A ⟶ N) (γ : N ⟶ (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
    (hsq : IsPushout α β ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) γ)
    (hmono : Mono (biprod.lift α (-β))) :
    ∃ δ : RB.obj (DerivedCategory.Q.obj M) ⟶ (DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk
          (biprod.lift (DerivedCategory.Q.map α ≫ unitQ B u K) (DerivedCategory.Q.map β))
          (biprod.desc (RB.map (DerivedCategory.Q.map ρ))
            (-(DerivedCategory.Q.map γ ≫ unitQ B u M))) δ ∈
        distTriang (DerivedCategory D) := by
  exact exists_distTriang_of_isPushout_of_resolution_aux B u R hu ρ hρ α β γ hsq hmono

/-- The resolution `R(X)` of an object `X` is K-injective. -/
instance (X : C) : (R.F.obj X).IsKInjective := CochainComplex.isKInjective_of_injective _ 0

omit [PreservesFiniteLimits B] in
include hu in
/-- **The cohomological hypothesis, read on the resolution.** If `RB(g[0])` is an isomorphism on
`H^q`, so is `B(R(g))`. -/
lemma isIso_homologyMap_of_isIso_homologyFunctor_map {X Y : C} (g : X ⟶ Y) (q : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor D q).map (RB.map (DerivedCategory.Q.map
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map g))))) :
    IsIso (homologyMap ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map g)) q) := by
  have hX := isIso_unitQ B u hu (R.F.obj X)
  have hY := isIso_unitQ B u hu (R.F.obj Y)
  set H := DerivedCategory.homologyFunctor D q
  have e₂ : RB.map (DerivedCategory.Q.map (R.F.map g)) =
      inv (RB.map (DerivedCategory.Q.map (R.ν.app X))) ≫
        RB.map (DerivedCategory.Q.map ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map g)) ≫
          RB.map (DerivedCategory.Q.map (R.ν.app Y)) := by
    rw [IsIso.eq_inv_comp, ← RB.map_comp, ← RB.map_comp, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_comp, R.ν.naturality]
  have hA : IsIso (H.map (RB.map (DerivedCategory.Q.map (R.F.map g)))) := by
    rw [e₂, H.map_comp, H.map_comp]
    infer_instance
  have e₁ : DerivedCategory.Q.map ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map g)) =
      unitQ B u (R.F.obj X) ≫ RB.map (DerivedCategory.Q.map (R.F.map g)) ≫
        inv (unitQ B u (R.F.obj Y)) := by
    rw [← Category.assoc, ← unitQ_naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hB : IsIso (H.map (DerivedCategory.Q.map
      ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map g)))) := by
    rw [e₁, H.map_comp, H.map_comp]
    infer_instance
  have e₀ := DerivedCategory.homologyFunctorFactors_hom_naturality
    ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map g)) q
  have e : IsIso ((DerivedCategory.homologyFunctorFactors D q).hom.app
        ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj (R.F.obj X)) ≫
      homologyMap ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.F.map g)) q) := by
    rw [← e₀]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hB
      ((DerivedCategory.homologyFunctorFactors D q).app _).isIso_hom
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    ((DerivedCategory.homologyFunctorFactors D q).app _).isIso_hom e

variable {B u hu} in
include hu in
/-- **The derived unit square of a left exact functor is homotopy cartesian.** Let `B` be a left
exact additive functor out of an abelian category with functorial injective embeddings, and
`RB` a right derived functor of `B` computed by K-injective complexes, with unit `u`. Let
`ρ : K ⟶ M` be a morphism of cochain complexes vanishing in negative degrees which induces
isomorphisms `H^q(RB(K^p)) ≅ H^q(RB(M^p))` for every `p` and every `q ≥ 1`. Then there is a
distinguished triangle `B(K) ⟶ RB(K) ⊞ B(M) ⟶ RB(M) ⟶ B(K)[1]` whose first map is `(u_K, B(ρ))`
and whose second is `(RB(ρ), -u_M)`. -/
theorem exists_distTriang (hC : HasFunctorialInjectiveEmbeddings C) {K M : CochainComplex C ℤ}
    [K.IsStrictlyGE 0] [M.IsStrictlyGE 0] (ρ : K ⟶ M)
    (hρ : ∀ (p q : ℤ), 0 < q → IsIso ((DerivedCategory.homologyFunctor D q).map
      (RB.map (DerivedCategory.Q.map ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map
        (ρ.f p)))))) :
    ∃ δ : RB.obj (DerivedCategory.Q.obj M) ⟶
        (DerivedCategory.Q.obj ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk
          (biprod.lift (unitQ B u K)
            (DerivedCategory.Q.map ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ)))
          (biprod.desc (RB.map (DerivedCategory.Q.map ρ)) (-unitQ B u M)) δ ∈
        distTriang (DerivedCategory D) := by
  obtain ⟨R⟩ := ColumnResolution.exists_functorialResolution hC
  exact exists_distTriang_of_resolution (hu := hu) (R := R) ρ (fun p q hq =>
    isIso_homologyMap_of_isIso_homologyFunctor_map B u hu R (ρ.f p) q (hρ p q hq))

variable {B u hu} in
include hu in
/-- **The derived unit square of a left exact functor, pasted with a bicartesian square, is
homotopy cartesian.** In the situation of `exists_distTriang`, if `α : A ⟶ B(K)`, `β : A ⟶ N`,
`B(ρ)` and `γ : N ⟶ B(M)` form a pushout square of complexes with `A ⟶ B(K) ⊞ N` a monomorphism,
there is a distinguished triangle `A ⟶ RB(K) ⊞ N ⟶ RB(M) ⟶ A[1]` whose first map is
`(u_K ∘ α, β)` and whose second is `(RB(ρ), -u_M ∘ γ)`. -/
theorem exists_distTriang_of_isPushout (hC : HasFunctorialInjectiveEmbeddings C)
    {K M : CochainComplex C ℤ} [K.IsStrictlyGE 0] [M.IsStrictlyGE 0] (ρ : K ⟶ M)
    (hρ : ∀ (p q : ℤ), 0 < q → IsIso ((DerivedCategory.homologyFunctor D q).map
      (RB.map (DerivedCategory.Q.map ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map
        (ρ.f p))))))
    {A N : CochainComplex D ℤ} (α : A ⟶ (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (β : A ⟶ N) (γ : N ⟶ (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
    (hsq : IsPushout α β ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) γ)
    (hmono : Mono (biprod.lift α (-β))) :
    ∃ δ : RB.obj (DerivedCategory.Q.obj M) ⟶ (DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk
          (biprod.lift (DerivedCategory.Q.map α ≫ unitQ B u K) (DerivedCategory.Q.map β))
          (biprod.desc (RB.map (DerivedCategory.Q.map ρ))
            (-(DerivedCategory.Q.map γ ≫ unitQ B u M))) δ ∈
        distTriang (DerivedCategory D) := by
  obtain ⟨R⟩ := ColumnResolution.exists_functorialResolution hC
  exact exists_distTriang_of_isPushout_of_resolution (hu := hu) (R := R) ρ (fun p q hq =>
    isIso_homologyMap_of_isIso_homologyFunctor_map B u hu R (ρ.f p) q (hρ p q hq)) α β γ hsq hmono

include hu in
/-- **For an exact functor the derived unit is invertible on every complex**, as soon as every
complex has a K-injective resolution. -/
lemma isIso_unitQ_of_preservesFiniteColimits [PreservesFiniteColimits B]
    (hres : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (φ : K ⟶ I),
      I.IsKInjective ∧ QuasiIso φ)
    (K : CochainComplex C ℤ) : IsIso (unitQ B u K) := by
  obtain ⟨I, φ, hI, hφ⟩ := hres K
  have h₁ := isIso_unitQ B u hu I
  have e := unitQ_naturality B u φ
  have : unitQ B u K = DerivedCategory.Q.map ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ≫
      unitQ B u I ≫ inv (RB.map (DerivedCategory.Q.map φ)) := by
    rw [reassoc_of% e, IsIso.hom_inv_id, Category.comp_id]
  rw [this]
  infer_instance

end Main

end StacksDraft.DerivedUnitSquare

end
