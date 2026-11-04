module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Algebra.Homology.SpectralSequence.FirstQuadrantDoubleComplex
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.CechFunctorAtFourUniverses

/-!
# The Čech-to-cohomology spectral sequence of a covering: the sequence and its second page

Let `X` be a space, `O` a sheaf of rings on `X`, and `𝒰` an indexed open covering of an open
`U ⊆ X`.  [Stacks, Tag 01ES] asks for a first-quadrant `E₂` cohomological spectral sequence,
functorial in the sheaf `F` of `O`-modules, whose second page is `Ȟ^p(𝒰, R^q i(F))` and which
abuts to `H^{p+q}(U, F)`.  This file supplies the first two of those three items: the functor
and the identification of its second page.  **The abutment is not here**, and nothing in this
file carries the tag `01ES`.

The input the general machinery of
`StacksFrontier/Algebra/Homology/SpectralSequence/FirstQuadrantDoubleComplex.lean` is waiting for is
the Čech double complex of an injective resolution,
```
K^{i,j}(F) = Č^j(𝒰, I^i(F)),
```
with the **resolution degree outer and the Čech degree inner**.  That orientation is forced: the
second spectral sequence of a double complex has `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))`, and
`H^q_I` is homology in the *first* (outer) index, so it is the resolution degree that has to be
differentiated first if `''E_2^{p,q}` is to come out as Čech cohomology of a derived functor.
Both indices are extended by zero from `ℕ` to `ℤ`, in the inner direction after the Čech complex
functor and in the outer direction after the resolution, which is what makes the first-quadrant
vanishing of `H^p_{II}(H^q_I(-))` immediate.

An injective resolution is functorial in the sheaf only up to homotopy, so `cechDouble` is not a
functor.  What it is is the object part of a functor up to filtered homotopy, which is exactly the
input of `HomologicalComplex₂.e₂FunctorOfHomotopyClasses`; the bridge from an honest homotopy in
the outer direction to the `FilteredHomotopy₂` that engine asks for is
`HomologicalComplex₂.filteredHomotopy₂_of_homotopy` below, and it is where the index orientation
pays off: a homotopy in the outer direction has components of degree `(-1, 0)`, which preserve the
filtration of the total complex by the *second* coordinate on the nose.

## Main definitions

* `ComplexShape.Embedding.extendFunctorHomologyIso`: extension by zero commutes with homology.
* `HomologicalComplex₂.totalHomotopy`: a homotopy between morphisms of double complexes, in the
  outer direction, induces a homotopy of the total complexes.
* `Stacks.Cohomology.CechSpectral.cechDoubleFunctor`: `Č^•(𝒰, -)` applied to a complex of
  sheaves of modules, as a double complex `K^{i,j} = Č^j(𝒰, -^i)` over `ℤ × ℤ`.
* `Stacks.Cohomology.CechSpectral.cechDouble`, `cechDoubleMap`: the same at the chosen injective
  resolution of a sheaf, together with the morphism induced by a morphism of sheaves.
* `Stacks.Cohomology.CechSpectral.cechE₂Functor`,
  `Stacks.Cohomology.CechSpectral.cechSpectralSequenceFunctor`: the resulting functorial `E₂`
  spectral sequence, on `ℤ × ℤ` and then on `ℕ × ℕ`.  The latter is the `sequence` field of
  `Stacks.Cohomology.CechSpectral.CechSpectralSequenceData`.

## Main results

* `HomologicalComplex₂.filteredHomotopy₂_of_homotopy`: an outer homotopy is a filtered homotopy.
* `Stacks.Cohomology.CechSpectral.cechDoubleXIso`: `K^{i,j}(F) = Č^j(𝒰, I^i(F))`, which records
  the index orientation.
* `Stacks.Cohomology.CechSpectral.isZero_homologyIIHomologyI_cechDouble`: the first-quadrant
  vanishing of `H^p_{II}(H^q_I(K^{•,•}(F)))`.
* `Stacks.Cohomology.CechSpectral.cechDoubleHomologyNatIso`: **the coefficient comparison**
  `H^p_{II}(H^q_I(K^{•,•}(-))) ≅ Ȟ^p(𝒰, H^q(-))` for a complex of sheaves, as a natural
  isomorphism of functors of that complex.  This is the half of the second-page identification
  that the spectral-sequence machinery does not supply: the Čech complex functor is exact, hence
  commutes with homology.
* `Stacks.Cohomology.CechSpectral.cechPageTwoIso`: the `pageTwoIso` field of
  `Stacks.Cohomology.CechSpectral.CechSpectralSequenceData`, i.e.
  `''E_2^{p,q} ≅ Ȟ^p(𝒰, R^q i(F))` naturally in `F`.

## Implementation notes

The existence of enough injectives, of sheafification for abelian presheaves and of the
description of the maps inverted by it are taken as hypotheses in the module universe
`max u r v w`, as in [Stacks, Tag 01ER]; `SheafOfModules.enoughInjectives`
`_opens` and its two companions in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GrothendieckAbelian.lean` discharge all three, so
this is not a restriction, only a way of not fixing the proof of abelianness inside these
definitions.

`CategoryTheory.SpectralSequence.natRestrictE₂Comp` is what converts the index type from `ℤ × ℤ`
to `ℕ × ℕ`.  `Stacks.Cohomology.CechSpectral.totalE₂SpectralSequenceNat₂Functor` cannot be
used: its first-quadrant hypothesis is
quantified over *every* double complex over the ambient category, which
`HomologicalComplex₂.not_forall_isFirstQuadrant` shows is unsatisfiable.

## References

* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
* [Stacks Project, Tag 01ER](https://stacks.math.columbia.edu/tag/01ER)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace ComplexShape.Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C]

/-- **Extension by zero preserves limits of any shape the target has.**  Limits of homological
complexes are computed degreewise, and in each degree the extension is either an evaluation or
zero. -/
instance extendFunctor_preservesLimitsOfShape
    (J : Type*) [Category* J] [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (e.extendFunctor C) :=
  HomologicalComplex.preservesLimitsOfShape_of_eval _ fun i' => by
    by_cases h : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := h
      exact preservesLimitsOfShape_of_natIso (e.extendFunctorCompEvalIso C hi).symm
    · refine Functor.preservesLimitsOfShape_of_isZero _ ?_ _
      rw [Functor.isZero_iff]
      exact fun K => K.isZero_extend_X e i' (by tauto)

/-- **Extension by zero preserves colimits of any shape the target has.** -/
instance extendFunctor_preservesColimitsOfShape
    (J : Type*) [Category* J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (e.extendFunctor C) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun i' => by
    by_cases h : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := h
      exact preservesColimitsOfShape_of_natIso (e.extendFunctorCompEvalIso C hi).symm
    · refine Functor.preservesColimitsOfShape_of_isZero _ ?_ _
      rw [Functor.isZero_iff]
      exact fun K => K.isZero_extend_X e i' (by tauto)

/-- Extension by zero along a complex-shape embedding preserves finite limits. -/
instance extendFunctor_preservesFiniteLimits [HasFiniteLimits C] :
    PreservesFiniteLimits (e.extendFunctor C) :=
  ⟨by intros; infer_instance⟩

/-- Extension by zero along a complex-shape embedding preserves finite colimits. -/
instance extendFunctor_preservesFiniteColimits [HasFiniteColimits C] :
    PreservesFiniteColimits (e.extendFunctor C) :=
  ⟨by intros; infer_instance⟩

/-- **Extension by zero commutes with homology.**  In the degrees in the image of the embedding
the homology of the extension is the homology of the original complex, naturally in the
complex. -/
def extendFunctorHomologyIso (D : Type*) [Category* D] [Abelian D] (j : ι) (j' : ι')
    (hj : e.f j = j') :
    e.extendFunctor D ⋙ HomologicalComplex.homologyFunctor D c' j' ≅
      HomologicalComplex.homologyFunctor D c j :=
  NatIso.ofComponents (fun K => K.extendHomologyIso e hj)
    (fun φ => HomologicalComplex.extendHomologyIso_hom_naturality φ e hj)

end ComplexShape.Embedding

namespace HomologicalComplex₂

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- `HomologicalComplex₂.ι_total_d` with the neighbouring indices supplied as hypotheses rather
than written out, so that it can be used at an index such as `i - 1` without a transport. -/
@[reassoc]
lemma ιTotal_total_d' {K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [K.HasTotal (ComplexShape.up ℤ)] (i i' j j' n n' : ℤ) (hi' : i + 1 = i') (hj' : j + 1 = j')
    (hij : i + j = n) (hn' : n + 1 = n') :
    K.ιTotal (ComplexShape.up ℤ) i j n (by dsimp; omega) ≫
        (K.total (ComplexShape.up ℤ)).d n n' =
      (K.d i i').f j ≫ K.ιTotal (ComplexShape.up ℤ) i' j n' (by dsimp; omega) +
        i.negOnePow • ((K.X i).d j j' ≫
          K.ιTotal (ComplexShape.up ℤ) i j' n' (by dsimp; omega)) := by
  obtain rfl : i' = i + 1 := by omega
  obtain rfl : j' = j + 1 := by omega
  obtain rfl : n' = n + 1 := by omega
  exact ι_total_d i j n hij

variable {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
  [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)] {Φ Ψ : K ⟶ L}

/-- The degree-`(n, m)` component of the homotopy of total complexes attached to a homotopy in
the outer direction: on the summand `K^{i,j}` it is the component of the given homotopy, landing
in the summand `L^{m - j, j}`.  The Čech degree `j` is untouched, which is why no sign is
needed and why the filtration by the second coordinate is preserved. -/
def totalHomotopyHom (H : Homotopy Φ Ψ) (n m : ℤ) :
    (K.total (ComplexShape.up ℤ)).X n ⟶ (L.total (ComplexShape.up ℤ)).X m :=
  K.totalDesc fun i j _ =>
    (H.hom i (m - j)).f j ≫ L.ιTotal (ComplexShape.up ℤ) (m - j) j m (by dsimp; omega)

/-- The value of `totalHomotopyHom` on the summand `K^{b,j}`, with the target summand named. -/
@[reassoc]
lemma ιTotal_totalHomotopyHom (H : Homotopy Φ Ψ) (a b j n m : ℤ) (hab : a + 1 = b)
    (hbj : b + j = n) (hm : m + 1 = n) :
    K.ιTotal (ComplexShape.up ℤ) b j n (by dsimp; omega) ≫ totalHomotopyHom H n m =
      (H.hom b a).f j ≫ L.ιTotal (ComplexShape.up ℤ) a j m (by dsimp; omega) := by
  obtain rfl : a = m - j := by omega
  exact K.ι_totalDesc _ b j _

/-- **A homotopy in the outer direction induces a homotopy of total complexes.**  No signs enter:
the sign `(-1)^i` carried by the vertical differential of the total complex changes by `-1` when
the outer degree drops by one, which is exactly what makes the two terms that would otherwise
obstruct the homotopy relation cancel. -/
def totalHomotopy (H : Homotopy Φ Ψ) :
    Homotopy (total.map Φ (ComplexShape.up ℤ)) (total.map Ψ (ComplexShape.up ℤ)) where
  hom := totalHomotopyHom H
  zero n m hnm := by
    refine total.hom_ext _ fun i j hij => ?_
    rw [comp_zero, totalHomotopyHom, K.ι_totalDesc _ i j hij,
      H.zero i (m - j) (fun h => hnm (show m + 1 = n by
        have h' : m - j + 1 = i := h
        dsimp at hij
        omega)), HomologicalComplex.zero_f, zero_comp]
  comm n := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by change n - 1 + 1 = n; omega)]
    refine total.hom_ext _ fun i j hij => ?_
    have hij' : i + j = n := hij
    have hcomm := H.comm i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by change i - 1 + 1 = i; omega)] at hcomm
    have hsucc := Int.negOnePow_succ (i - 1)
    rw [show i - 1 + 1 = i by omega] at hsucc
    have hneg : ((i - 1 : ℤ)).negOnePow = - i.negOnePow := by rw [hsucc, neg_neg]
    have e1 : K.ιTotal (ComplexShape.up ℤ) i j n hij ≫
          ((K.total (ComplexShape.up ℤ)).d n (n + 1) ≫ totalHomotopyHom H (n + 1) n) =
        (K.d i (i + 1)).f j ≫ (H.hom (i + 1) i).f j ≫
            L.ιTotal (ComplexShape.up ℤ) i j n hij +
          i.negOnePow • ((K.X i).d j (j + 1) ≫ (H.hom i (i - 1)).f (j + 1) ≫
            L.ιTotal (ComplexShape.up ℤ) (i - 1) (j + 1) n (by dsimp; omega)) := by
      rw [← Category.assoc,
        ιTotal_total_d' i (i + 1) j (j + 1) n (n + 1) rfl rfl hij' rfl,
        Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, Category.assoc,
        ιTotal_totalHomotopyHom H i (i + 1) j (n + 1) n (by omega) (by omega) (by omega),
        ιTotal_totalHomotopyHom H (i - 1) i (j + 1) (n + 1) n (by omega) (by omega) (by omega)]
    have e2 : K.ιTotal (ComplexShape.up ℤ) i j n hij ≫
          (totalHomotopyHom H n (n - 1) ≫ (L.total (ComplexShape.up ℤ)).d (n - 1) n) =
        (H.hom i (i - 1)).f j ≫ (L.d (i - 1) i).f j ≫
            L.ιTotal (ComplexShape.up ℤ) i j n hij +
          (i - 1).negOnePow • ((H.hom i (i - 1)).f j ≫ (L.X (i - 1)).d j (j + 1) ≫
            L.ιTotal (ComplexShape.up ℤ) (i - 1) (j + 1) n (by dsimp; omega)) := by
      rw [← Category.assoc,
        ιTotal_totalHomotopyHom H (i - 1) i j n (n - 1) (by omega) hij' (by omega),
        Category.assoc,
        ιTotal_total_d' (i - 1) i j (j + 1) (n - 1) n (by omega) rfl (by omega) (by omega),
        Preadditive.comp_add, Linear.comp_units_smul]
    rw [ιTotal_map, Preadditive.comp_add, Preadditive.comp_add, e1, e2, ιTotal_map, hcomm,
      HomologicalComplex.add_f_apply, HomologicalComplex.add_f_apply,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f, Preadditive.add_comp,
      Preadditive.add_comp, Category.assoc, Category.assoc, hneg,
      HomologicalComplex.Hom.comm_assoc]
    simp only [Units.neg_smul]
    abel

/-- The homotopy of total complexes attached to an outer homotopy carries the step
`⨁_{j ≥ p} K^{i,j}` of the filtration by the second coordinate into the corresponding step of
the target, because its components do not change the second coordinate. -/
lemma totalProjector_totalHomotopyHom (H : Homotopy Φ Ψ) (p n m : ℤ) :
    K.totalProjector (fun _ j => p ≤ j) n ≫ totalHomotopyHom H n m ≫
        L.totalProjector (fun _ j => p ≤ j) m =
      K.totalProjector (fun _ j => p ≤ j) n ≫ totalHomotopyHom H n m := by
  refine total.hom_ext _ fun i j hij => ?_
  rw [ι_totalProjector_assoc, ι_totalProjector_assoc]
  split_ifs with hP
  · rw [totalHomotopyHom, K.ι_totalDesc_assoc _ i j hij, K.ι_totalDesc _ i j hij,
      Category.assoc, ι_totalProjector, ite_eq_left hP]
  · rw [zero_comp, zero_comp]

/-- **An honest homotopy in the outer direction is a filtered homotopy.**  The components of the
homotopy have degree `(-1, 0)`, which preserves the filtration of the total complex by the second
coordinate. -/
lemma filteredHomotopy₂_of_homotopy (H : Homotopy Φ Ψ) : FilteredHomotopy₂ Φ Ψ :=
  ⟨totalHomotopy H, fun p n m =>
    Subobject.exists_le_of_comm _
      (Subobject.factorThru _
        ((K.stepSubobject (fun (_ : ℤ) j => j) p n).arrow ≫ totalHomotopyHom H n m)
        (imageSubobject_factors_arrow_comp_of_comp_eq _ _ _
          (totalProjector_totalHomotopyHom H p n m)))
      (Subobject.factorThru_arrow _ _ _)⟩

end HomologicalComplex₂

namespace Stacks.Cohomology.CechSpectral

universe u r v w

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, w} (TopCat.of X))

/-- The Čech complex functor of the cover `𝒰` preserves finite limits. -/
instance cechComplexFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (cechComplexFunctor.{u, r, v, w} O 𝒰) :=
  (CechExactFunctor.presheafCechComplexFunctor_exact.{u, r, max u r v w, w}
    O.obj 𝒰.U 𝒰.obj 𝒰.le).1

/-- The Čech complex functor of the cover `𝒰` preserves finite colimits. -/
instance cechComplexFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (cechComplexFunctor.{u, r, v, w} O 𝒰) :=
  (CechExactFunctor.presheafCechComplexFunctor_exact.{u, r, max u r v w, w}
    O.obj 𝒰.U 𝒰.obj 𝒰.le).2

/-- The Čech complex functor of the cover `𝒰` preserves homology. -/
instance cechComplexFunctor_preservesHomology :
    (cechComplexFunctor.{u, r, v, w} O 𝒰).PreservesHomology :=
  inferInstance

/-- **The Čech double complex of a complex of sheaves of `O`-modules, over `ℕ × ℕ`**: in
bidegree `(i, j)` the `j`-th term of the Čech complex of the `i`-th term of the given complex.
The **degree in the given complex is the outer index and the Čech degree the inner one**; see the
module documentation for why that is forced. -/
def cechDoubleNatFunctor :
    CochainComplex (SheafOfModules.{max u r v w} O) ℕ ⥤
      HomologicalComplex
        (CochainComplex (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℕ)
        (ComplexShape.up ℕ) :=
  (SheafOfModules.forget.{max u r v w} O).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    (cechComplexFunctor.{u, r, v, w} O 𝒰).mapHomologicalComplex (ComplexShape.up ℕ)

/-- `cechDoubleNatFunctor` with the outer index extended by zero to `ℤ`. -/
def cechDoubleOuterFunctor :
    CochainComplex (SheafOfModules.{max u r v w} O) ℕ ⥤
      HomologicalComplex
        (CochainComplex (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℕ)
        (ComplexShape.up ℤ) :=
  cechDoubleNatFunctor.{u, r, v, w} O 𝒰 ⋙
    ComplexShape.embeddingUpNat.extendFunctor
      (CochainComplex (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℕ)

/-- **The Čech double complex of a complex of sheaves of `O`-modules**, over `ℤ × ℤ`: both
indices of `cechDoubleNatFunctor` extended by zero. -/
def cechDoubleFunctor :
    CochainComplex (SheafOfModules.{max u r v w} O) ℕ ⥤
      HomologicalComplex₂ (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  cechDoubleOuterFunctor.{u, r, v, w} O 𝒰 ⋙
    (ComplexShape.embeddingUpNat.extendFunctor
      (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The index convention of `cechDoubleFunctor`**: in bidegree `((i : ℤ), (j : ℤ))` with
`i j : ℕ` it is the `j`-th term of the Čech complex of the `i`-th term of the complex. -/
def cechDoubleFunctorXIso (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) (i j : ℕ)
    (i' j' : ℤ) (hi : (i : ℤ) = i') (hj : (j : ℤ) = j') :
    (((cechDoubleFunctor.{u, r, v, w} O 𝒰).obj Y).X i').X j' ≅
      ((cechComplexFunctor.{u, r, v, w} O 𝒰).obj
        ((SheafOfModules.forget O).obj (Y.X i))).X j :=
  HomologicalComplex.extendXIso (((cechDoubleOuterFunctor.{u, r, v, w} O 𝒰).obj Y).X i')
      ComplexShape.embeddingUpNat hj ≪≫
    (HomologicalComplex.eval (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))
        (ComplexShape.up ℕ) j).mapIso
      (HomologicalComplex.extendXIso ((cechDoubleNatFunctor.{u, r, v, w} O 𝒰).obj Y)
        ComplexShape.embeddingUpNat hi)

/-- A homotopy between morphisms of complexes of sheaves induces a homotopy between the induced
morphisms of Čech double complexes: each of the four functors making up `cechDoubleFunctor` is
additive, and extension by zero carries homotopies to homotopies. -/
def cechDoubleFunctorHomotopy {Y Z : CochainComplex (SheafOfModules.{max u r v w} O) ℕ}
    {φ ψ : Y ⟶ Z} (H : Homotopy φ ψ) :
    Homotopy ((cechDoubleFunctor.{u, r, v, w} O 𝒰).map φ)
      ((cechDoubleFunctor.{u, r, v, w} O 𝒰).map ψ) :=
  (ComplexShape.embeddingUpNat.extendFunctor
    (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).mapHomotopy
      (((cechComplexFunctor.{u, r, v, w} O 𝒰).mapHomotopy
        ((SheafOfModules.forget.{max u r v w} O).mapHomotopy H)).extend
          ComplexShape.embeddingUpNat)

/-- **The coefficient half of the second-page identification.**  Taking the homology of the Čech
double complex of a complex of sheaves, first in the resolution direction and then in the Čech
direction, is Čech cohomology of the homology of the complex, naturally in the complex.  This is
the statement that the Čech complex functor commutes with homology, which it does because it is
exact ([Stacks, Tag 01EJ]), together with the fact that extension by zero does. -/
def cechDoubleHomologyNatIso (p q : ℕ) :
    cechDoubleFunctor.{u, r, v, w} O 𝒰 ⋙
        HomologicalComplex₂.homologyIIHomologyIFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (p : ℤ) (q : ℤ) ≅
      (SheafOfModules.forget.{max u r v w} O).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor (PresheafOfModules.{max u r v w} O.obj)
            (ComplexShape.up ℕ) q ⋙
          cechCohomologyFunctor.{u, r, v, w} O 𝒰 p :=
  Functor.isoWhiskerLeft (cechDoubleOuterFunctor.{u, r, v, w} O 𝒰)
      (Functor.isoWhiskerRight
          (Functor.mapHomologicalComplexHomologyIso
            (ComplexShape.embeddingUpNat.extendFunctor
              (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))) (ComplexShape.up ℤ) (q : ℤ))
          (HomologicalComplex.homologyFunctor
            (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (ComplexShape.up ℤ) (p : ℤ)) ≪≫
        Functor.isoWhiskerLeft
          (HomologicalComplex.homologyFunctor
            (CochainComplex (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℕ)
            (ComplexShape.up ℤ) (q : ℤ))
          (ComplexShape.embeddingUpNat.extendFunctorHomologyIso
            (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) p (p : ℤ) rfl)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (cechDoubleNatFunctor.{u, r, v, w} O 𝒰)
        (ComplexShape.embeddingUpNat.extendFunctorHomologyIso
          (CochainComplex (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℕ) q (q : ℤ) rfl))
      (HomologicalComplex.homologyFunctor
        (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (ComplexShape.up ℕ) p) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((SheafOfModules.forget.{max u r v w} O).mapHomologicalComplex (ComplexShape.up ℕ))
        (Functor.mapHomologicalComplexHomologyIso (cechComplexFunctor.{u, r, v, w} O 𝒰)
          (ComplexShape.up ℕ) q))
      (HomologicalComplex.homologyFunctor
        (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (ComplexShape.up ℕ) p)

/-- **First-quadrant vanishing for the Čech double complex.**  Both indices are extended by zero
from `ℕ`, so `H^p_{II}(H^q_I(K^{•,•}))` vanishes as soon as `p < 0` or `q < 0`: in the first case
the complex `H^q_I(K^{•,•})` is zero in degree `p`, in the second the outer complex is exact at
`q`. -/
lemma isZero_homologyIIHomologyI_cechDoubleFunctor
    (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero ((HomologicalComplex₂.homologyIIHomologyIFunctor
      (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) p q).obj
        ((cechDoubleFunctor.{u, r, v, w} O 𝒰).obj Y)) := by
  refine (Iso.isZero_iff ((HomologicalComplex.homologyFunctor
      (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (ComplexShape.up ℤ) p).mapIso
    ((Functor.mapHomologicalComplexHomologyIso
      (ComplexShape.embeddingUpNat.extendFunctor
        (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))) (ComplexShape.up ℤ) q).app
      ((cechDoubleOuterFunctor.{u, r, v, w} O 𝒰).obj Y)))).2 ?_
  rcases h with hp | hq
  · refine (HomologicalComplex.exactAt_iff_isZero_homology
      ((((cechDoubleOuterFunctor.{u, r, v, w} O 𝒰).obj Y).homology q).extend
        ComplexShape.embeddingUpNat) p).1 (ShortComplex.exact_of_isZero_X₂ _ ?_)
    exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
      fun i => by change ((i : ℕ) : ℤ) ≠ p; omega
  · refine Functor.map_isZero (HomologicalComplex.homologyFunctor
      (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (ComplexShape.up ℤ) p)
      (Functor.map_isZero (ComplexShape.embeddingUpNat.extendFunctor
        (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))) ?_)
    refine (HomologicalComplex.exactAt_iff_isZero_homology
      ((cechDoubleOuterFunctor.{u, r, v, w} O 𝒰).obj Y) q).1 ?_
    exact HomologicalComplex.extend_exactAt ((cechDoubleNatFunctor.{u, r, v, w} O 𝒰).obj Y)
      ComplexShape.embeddingUpNat q fun j => by change ((j : ℕ) : ℤ) ≠ q; omega

section Resolution

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u r v w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u r v w}]
  [EnoughInjectives (SheafOfModules.{max u r v w} O)]

/-- **The Čech double complex of a sheaf of `O`-modules**: `K^{i,j}(F) = Č^j(𝒰, I^i(F))` for the
chosen injective resolution `I^•(F)` of `F`, with the resolution degree outer. -/
def cechDouble (F : SheafOfModules.{max u r v w} O) :
    HomologicalComplex₂ (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (cechDoubleFunctor.{u, r, v, w} O 𝒰).obj (injectiveResolution F).cocomplex

/-- The morphism of Čech double complexes attached to a morphism of sheaves: the double complex
of a chosen descent of that morphism to the chosen injective resolutions.  This is functorial
only up to homotopy, which is all `HomologicalComplex₂.e₂FunctorOfHomotopyClasses` needs. -/
def cechDoubleMap {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) :
    cechDouble.{u, r, v, w} O 𝒰 F ⟶ cechDouble.{u, r, v, w} O 𝒰 G :=
  (cechDoubleFunctor.{u, r, v, w} O 𝒰).map
    (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))

/-- `cechDoubleMap` sends an identity to a filtered homotopy class of the identity. -/
lemma filteredHomotopy₂_cechDoubleMap_id (F : SheafOfModules.{max u r v w} O) :
    HomologicalComplex₂.FilteredHomotopy₂ (cechDoubleMap.{u, r, v, w} O 𝒰 (𝟙 F)) (𝟙 _) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    ((cechDoubleFunctorHomotopy.{u, r, v, w} O 𝒰
        (InjectiveResolution.descIdHomotopy F (injectiveResolution F))).trans
      (Homotopy.ofEq ((cechDoubleFunctor.{u, r, v, w} O 𝒰).map_id _)))

/-- `cechDoubleMap` is multiplicative up to filtered homotopy. -/
lemma filteredHomotopy₂_cechDoubleMap_comp {F G H : SheafOfModules.{max u r v w} O}
    (f : F ⟶ G) (g : G ⟶ H) :
    HomologicalComplex₂.FilteredHomotopy₂ (cechDoubleMap.{u, r, v, w} O 𝒰 (f ≫ g))
      (cechDoubleMap.{u, r, v, w} O 𝒰 f ≫ cechDoubleMap.{u, r, v, w} O 𝒰 g) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    ((cechDoubleFunctorHomotopy.{u, r, v, w} O 𝒰
        (InjectiveResolution.descCompHomotopy f g (injectiveResolution F)
          (injectiveResolution G) (injectiveResolution H))).trans
      (Homotopy.ofEq ((cechDoubleFunctor.{u, r, v, w} O 𝒰).map_comp _ _)))

/-- **The Čech-to-cohomology spectral sequence on `ℤ × ℤ`**, functorial in the sheaf: the second
spectral sequence of the Čech double complex of an injective resolution, presented from its
second page. -/
def cechE₂Functor :
    SheafOfModules.{max u r v w} O ⥤
      E₂CohomologicalSpectralSequence (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) :=
  HomologicalComplex₂.e₂FunctorOfHomotopyClasses (cechDouble.{u, r, v, w} O 𝒰)
    (cechDoubleMap.{u, r, v, w} O 𝒰) (filteredHomotopy₂_cechDoubleMap_id.{u, r, v, w} O 𝒰)
    (fun f g => filteredHomotopy₂_cechDoubleMap_comp.{u, r, v, w} O 𝒰 f g)

/-- The Čech spectral sequence of a sheaf is first quadrant from its second page on. -/
lemma isFirstQuadrant_cechE₂Functor (F : SheafOfModules.{max u r v w} O) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => (r, 1 - r))
      ((cechE₂Functor.{u, r, v, w} O 𝒰).obj F) :=
  HomologicalComplex₂.isFirstQuadrant_e₂SpectralSequence₂Functor _
    (cechDouble.{u, r, v, w} O 𝒰 F) fun p q h =>
      isZero_homologyIIHomologyI_cechDoubleFunctor.{u, r, v, w} O 𝒰 _ p q h

/-- **The `sequence` field of `Stacks.Cohomology.CechSpectral.CechSpectralSequenceData`**: the
functorial first-quadrant `E₂` cohomological spectral sequence of the covering `𝒰`, carried on
`ℕ × ℕ`. -/
def cechSpectralSequenceFunctor :
    SheafOfModules.{max u r v w} O ⥤
      E₂CohomologicalSpectralSequenceNat (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) :=
  CategoryTheory.SpectralSequence.natRestrictE₂Comp (cechE₂Functor.{u, r, v, w} O 𝒰)
    (isFirstQuadrant_cechE₂Functor.{u, r, v, w} O 𝒰)

/-- **[Stacks, Tag 0130] (6) for the Čech spectral sequence.**  The second page of
`cechE₂Functor` at `((p : ℤ), (q : ℤ))` is `H^p_{II}(H^q_I(K^{•,•}(F)))`. -/
def cechPageTwoAppIso (p q : ℕ) (F : SheafOfModules.{max u r v w} O) :
    (cechE₂Functor.{u, r, v, w} O 𝒰 ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ))).obj F ≅
      (HomologicalComplex₂.homologyIIHomologyIFunctor
        (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (p : ℤ) (q : ℤ)).obj
          (cechDouble.{u, r, v, w} O 𝒰 F) :=
  HomologicalComplex₂.isoTwoPageTotalFiltration₂ (cechDouble.{u, r, v, w} O 𝒰 F) _
    (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) (p : ℤ) (q : ℤ)

/-- `cechPageTwoAppIso` is natural in the sheaf, for the morphisms `cechDoubleMap` of double
complexes.  This is `HomologicalComplex₂.pageTwoIso_naturality_of_homotopyClasses`. -/
lemma cechPageTwoAppIso_naturality (p q : ℕ) {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) :
    (cechE₂Functor.{u, r, v, w} O 𝒰 ⋙
          CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
            HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ))).map f ≫
        (cechPageTwoAppIso.{u, r, v, w} O 𝒰 p q G).hom =
      (cechPageTwoAppIso.{u, r, v, w} O 𝒰 p q F).hom ≫
        (HomologicalComplex₂.homologyIIHomologyIFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (p : ℤ) (q : ℤ)).map
            (cechDoubleMap.{u, r, v, w} O 𝒰 f) :=
  HomologicalComplex₂.pageTwoIso_naturality_of_homotopyClasses
    (cechDouble.{u, r, v, w} O 𝒰) (cechDoubleMap.{u, r, v, w} O 𝒰)
    (filteredHomotopy₂_cechDoubleMap_id.{u, r, v, w} O 𝒰)
    (fun f g => filteredHomotopy₂_cechDoubleMap_comp.{u, r, v, w} O 𝒰 f g) f (p : ℤ) (q : ℤ)

/-- `cechDoubleHomologyNatIso` at the chosen injective resolution of a sheaf, with its type
written in the form the second page of the spectral sequence has. -/
def cechDoubleHomologyIso (p q : ℕ) (F : SheafOfModules.{max u r v w} O) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
        (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (p : ℤ) (q : ℤ)).obj
          (cechDouble.{u, r, v, w} O 𝒰 F) ≅
      (cechCohomologyFunctor.{u, r, v, w} O 𝒰 p).obj
        ((HomologicalComplex.homologyFunctor (PresheafOfModules.{max u r v w} O.obj)
          (ComplexShape.up ℕ) q).obj
            (((SheafOfModules.forget.{max u r v w} O).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)) :=
  (cechDoubleHomologyNatIso.{u, r, v, w} O 𝒰 p q).app (injectiveResolution F).cocomplex

/-- `cechDoubleHomologyIso` read as a naturality square for `cechDoubleMap`. -/
lemma cechDoubleHomologyIso_naturality (p q : ℕ) {F G : SheafOfModules.{max u r v w} O}
    (f : F ⟶ G) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (p : ℤ) (q : ℤ)).map
          (cechDoubleMap.{u, r, v, w} O 𝒰 f) ≫
        (cechDoubleHomologyIso.{u, r, v, w} O 𝒰 p q G).hom =
      (cechDoubleHomologyIso.{u, r, v, w} O 𝒰 p q F).hom ≫
        (cechCohomologyFunctor.{u, r, v, w} O 𝒰 p).map
          ((HomologicalComplex.homologyFunctor (PresheafOfModules.{max u r v w} O.obj)
            (ComplexShape.up ℕ) q).map
              (((SheafOfModules.forget.{max u r v w} O).mapHomologicalComplex
                (ComplexShape.up ℕ)).map
                  (InjectiveResolution.desc f (injectiveResolution G)
                    (injectiveResolution F)))) :=
  (cechDoubleHomologyNatIso.{u, r, v, w} O 𝒰 p q).hom.naturality _

/-- **The coefficient comparison at a sheaf**: `H^p_{II}(H^q_I(K^{•,•}(F))) ≅ Ȟ^p(𝒰, R^q i(F))`.
This is `cechDoubleHomologyIso` followed by the computation of `R^q i(F)` by the chosen injective
resolution of `F`. -/
@[simps]
def cechCoefficientIso (p q : ℕ) (F : SheafOfModules.{max u r v w} O) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
        (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (p : ℤ) (q : ℤ)).obj
          (cechDouble.{u, r, v, w} O 𝒰 F) ≅
      ((SheafOfModules.forget.{max u r v w} O).rightDerived q ⋙
        cechCohomologyFunctor.{u, r, v, w} O 𝒰 p).obj F where
  hom := (cechDoubleHomologyIso.{u, r, v, w} O 𝒰 p q F).hom ≫
    (cechCohomologyFunctor.{u, r, v, w} O 𝒰 p).map
      ((injectiveResolution F).isoRightDerivedObj
        (SheafOfModules.forget.{max u r v w} O) q).inv
  inv := (cechCohomologyFunctor.{u, r, v, w} O 𝒰 p).map
      ((injectiveResolution F).isoRightDerivedObj
        (SheafOfModules.forget.{max u r v w} O) q).hom ≫
    (cechDoubleHomologyIso.{u, r, v, w} O 𝒰 p q F).inv
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc
      ((cechCohomologyFunctor.{u, r, v, w} O 𝒰 p).map _), ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc
      ((cechDoubleHomologyIso.{u, r, v, w} O 𝒰 p q F).inv), Iso.inv_hom_id,
      Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl

/-- The coefficient comparison is natural in the sheaf, for the morphisms `cechDoubleMap` of
double complexes. -/
lemma cechCoefficientIso_naturality (p q : ℕ) {F G : SheafOfModules.{max u r v w} O}
    (f : F ⟶ G) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (p : ℤ) (q : ℤ)).map
          (cechDoubleMap.{u, r, v, w} O 𝒰 f) ≫
        (cechCoefficientIso.{u, r, v, w} O 𝒰 p q G).hom =
      (cechCoefficientIso.{u, r, v, w} O 𝒰 p q F).hom ≫
        ((SheafOfModules.forget.{max u r v w} O).rightDerived q ⋙
          cechCohomologyFunctor.{u, r, v, w} O 𝒰 p).map f := by
  have h3 := InjectiveResolution.isoRightDerivedObj_inv_naturality f
    (injectiveResolution F) (injectiveResolution G) _
    (InjectiveResolution.desc_commutes_zero f (injectiveResolution G)
      (injectiveResolution F)) (SheafOfModules.forget.{max u r v w} O) q
  dsimp only [Functor.comp_map] at h3
  rw [cechCoefficientIso_hom, cechCoefficientIso_hom,
    reassoc_of% cechDoubleHomologyIso_naturality.{u, r, v, w} O 𝒰 p q f, ← Functor.map_comp]
  dsimp only [Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp, h3]

/-- **The second page of the Čech spectral sequence, on `ℤ × ℤ`.**  At `((p : ℤ), (q : ℤ))` it
is `Ȟ^p(𝒰, R^q i(F))`, naturally in `F`: the spectral-sequence identification
`''E_2^{p,q} ≅ H^p_{II}(H^q_I(K^{•,•}(F)))` of [Stacks, Tag 0130] (6), followed by the
coefficient comparison. -/
def cechPageTwoIsoInt (p q : ℕ) :
    cechE₂Functor.{u, r, v, w} O 𝒰 ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ)) ≅
      (SheafOfModules.forget.{max u r v w} O).rightDerived q ⋙
        cechCohomologyFunctor.{u, r, v, w} O 𝒰 p :=
  NatIso.ofComponents
    (fun F => cechPageTwoAppIso.{u, r, v, w} O 𝒰 p q F ≪≫
      cechCoefficientIso.{u, r, v, w} O 𝒰 p q F)
    (fun f => by
      rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
        cechPageTwoAppIso_naturality.{u, r, v, w} O 𝒰 p q f, Category.assoc,
        cechCoefficientIso_naturality.{u, r, v, w} O 𝒰 p q f, Category.assoc])

/-- **The `pageTwoIso` field of `Stacks.Cohomology.CechSpectral.CechSpectralSequenceData`**: the
second page of the
Čech spectral sequence at `(p, q) : ℕ × ℕ` is `Ȟ^p(𝒰, R^q i(F))`, naturally in the sheaf `F`.
The passage from `ℤ × ℤ` to `ℕ × ℕ` is on the nose, by
`CategoryTheory.SpectralSequence.natRestrictE₂Comp_pageTwoIso`. -/
def cechPageTwoIso (p q : ℕ) :
    cechSpectralSequenceFunctor.{u, r, v, w} O 𝒰 ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ (p, q) ≅
      (SheafOfModules.forget.{max u r v w} O).rightDerived q ⋙
        cechCohomologyFunctor.{u, r, v, w} O 𝒰 p :=
  CategoryTheory.SpectralSequence.natRestrictE₂Comp_pageTwoIso
      (cechE₂Functor.{u, r, v, w} O 𝒰) (isFirstQuadrant_cechE₂Functor.{u, r, v, w} O 𝒰) p q ≪≫
    cechPageTwoIsoInt.{u, r, v, w} O 𝒰 p q

end Resolution

end Stacks.Cohomology.CechSpectral

end
