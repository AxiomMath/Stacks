module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedInternalHomCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentExtensionOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentSectionUniverseLift
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.RaisedTermwiseSplit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.QuasiIsoInvariance
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.RaisedUnitSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence of the cohomology of the internal Hom out of a strictly perfect complex

Let `(C, O)` be a ringed site, let `P` be a strictly perfect complex of `O`-modules (Stacks 08FL)
and let `L` be a complex of `O`-modules all of whose cohomology sheaves are coherent. Then every
cohomology sheaf of the internal Hom complex `SheafHom(P, L)` of Stacks 0A8Z is coherent.

No hypothesis on the structure sheaf is needed, and none on `L` beyond the coherence of its
cohomology: `L` need not be K-injective, bounded or anything else.

## The dévissage

Coherent modules on a ringed site form a weak Serre subcategory: they contain `0`, are closed
under isomorphisms, kernels and cokernels (Stacks 01BY (3)) and extensions (Stacks 01BY (4)).
So the middle term of a five term exact sequence whose four outer terms are coherent is
coherent (`Stacks.SheafOfModules.isCoherentOnSite_of_exact₅`), and coherent modules are closed
under retracts. The internal Hom complex out of a termwise split short complex of sources is
short exact (`AlgebraicGeometry.RingedSite.Raised.internalHomShortComplex_shortExact`), so its
long exact cohomology sequence lets coherence pass from the outer sources to the middle one. The
induction then runs as in the proof of Stacks 08JH:

* a source concentrated in one degree `k` with that term `O`: the internal Hom complex is the
  universe lift of `L` shifted by `k` on three-term truncations
  (`AlgebraicGeometry.RingedSite.Raised.homUnitShortComplexIso`), and the universe lift is exact
  and preserves coherence;
* a source concentrated in one degree with that term `O^{⊕r}`, by induction on `r` through the
  split short complexes `O^{⊕r} ⟶ O^{⊕(r+1)} ⟶ O`;
* a source concentrated in one degree with that term a direct summand of a finite free module,
  by passing to a retract;
* a bounded source with such terms, by induction on the length of the window where it may be
  nonzero, splitting off its lowest term.

## Main results

* `Stacks.SheafOfModules.isCoherentOnSite_of_exact₅`: the weak Serre property of coherent
  modules on a site, Stacks 02MO (2), at a module universe independent of that of the rings.
* `RingedSite.Raised.isCoherentOnSite_homology_sheafHomComplex_of_isStrictlyPerfect` (in the
  namespace `AlgebraicGeometry`): **the cohomology of `SheafHom(P, L)` is coherent** for `P`
  strictly perfect and `L` with coherent cohomology.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe m u v w c

/-! ### Coherent modules form a weak Serre subcategory -/

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

/-- **Stacks 02MO (2) for coherent modules on a site.** In an exact sequence
`A₀ ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄` of sheaves of modules whose four outer terms are coherent, the middle
term is coherent.

The middle term is an extension of `Ker(A₃ ⟶ A₄)` by `Coker(A₀ ⟶ A₁)`, and coherence is closed
under kernels and cokernels (Stacks 01BY (3)) and extensions (Stacks 01BY (4)). -/
theorem isCoherentOnSite_of_exact₅ {A₀ A₁ A₂ A₃ A₄ : SheafOfModules.{m} R}
    {f₀ : A₀ ⟶ A₁} {f₁ : A₁ ⟶ A₂} {f₂ : A₂ ⟶ A₃} {f₃ : A₃ ⟶ A₄}
    (w₀ : f₀ ≫ f₁ = 0) (w₁ : f₁ ≫ f₂ = 0) (w₂ : f₂ ≫ f₃ = 0)
    (e₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (e₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (e₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (h₀ : _root_.SheafOfModules.IsCoherentOnSite A₀)
    (h₁ : _root_.SheafOfModules.IsCoherentOnSite A₁)
    (h₃ : _root_.SheafOfModules.IsCoherentOnSite A₃)
    (h₄ : _root_.SheafOfModules.IsCoherentOnSite A₄) :
    _root_.SheafOfModules.IsCoherentOnSite A₂ := by
  have hmono : Mono (cokernel.desc _ _ w₀) := e₀.mono_cokernelDesc
  have hepi : Epi (kernel.lift _ _ w₂) := e₂.epi_kernelLift
  have wM : cokernel.desc _ _ w₀ ≫ f₂ = 0 := by
    rw [← cancel_epi (cokernel.π f₀), cokernel.π_desc_assoc, comp_zero, w₁]
  have hM : (ShortComplex.mk (cokernel.desc _ _ w₀) f₂ wM).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk f₁ f₂ w₁)
      (S₂ := ShortComplex.mk (cokernel.desc _ _ w₀) f₂ wM)
      ⟨cokernel.π _, 𝟙 _, 𝟙 _, by simp, by simp⟩).1 e₁
  have hz : cokernel.desc _ _ w₀ ≫ kernel.lift _ _ w₂ = 0 := by
    rw [← cancel_mono (kernel.ι f₃)]
    simp [wM]
  have hSE : (ShortComplex.mk _ _ hz).ShortExact :=
    ShortComplex.ShortExact.mk'
      ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        (S₁ := ShortComplex.mk (cokernel.desc _ _ w₀) (kernel.lift _ _ w₂) hz)
        (S₂ := ShortComplex.mk (cokernel.desc _ _ w₀) f₂ wM)
        ⟨𝟙 _, 𝟙 _, kernel.ι _, by simp, by simp⟩).2 hM) hmono hepi
  exact isCoherentOnSite_X₂_of_shortExact hSE (isCoherentOnSite_cokernel' f₀ h₀ h₁)
    (isCoherentOnSite_kernel h₃ h₄ f₃)

/-- Coherent modules on a site form a weak Serre subcategory in the sense of Stacks 02MO (2). -/
@[sga "6 IV 2.4" "more general"]
theorem isWeakSerre_isCoherentOnSite :
    WeakSerre.IsWeakSerre
      (fun M : SheafOfModules.{m} R => _root_.SheafOfModules.IsCoherentOnSite M) where
  isClosedUnderIsomorphisms := ⟨fun e h => isCoherentOnSite_of_iso e h⟩
  nonempty := ⟨0, isCoherentOnSite_zero (isZero_zero _)⟩
  mem_of_exact5 E h₀ h₁ h₃ h₄ :=
    isCoherentOnSite_of_exact₅ E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄

/-- A retract of a coherent module on a site is coherent. -/
theorem isCoherentOnSite_of_retract {M N : SheafOfModules.{m} R} (h : Retract M N)
    (hN : _root_.SheafOfModules.IsCoherentOnSite N) :
    _root_.SheafOfModules.IsCoherentOnSite M :=
  DerivedCategoryB.retract_mem_of_isWeakSerre _ isWeakSerre_isCoherentOnSite h hN

end Stacks.SheafOfModules

/-! ### The dévissage over a strictly perfect source -/

namespace AlgebraicGeometry.RingedSite.Raised

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (L : CochainComplex (SheafOfModules.{w} (ringSheaf X.O)) ℤ)

/-- Every cohomology sheaf of the internal Hom complex `SheafHom(E, L)` is coherent. -/
def HomHomologyCoherent (E : CochainComplex (SheafOfModules.{w} (ringSheaf X.O)) ℤ) : Prop :=
  ∀ j : ℤ, SheafOfModules.IsCoherentOnSite ((sheafHomComplex X E L).obj.homology j)

variable {X L}

/-- The isomorphism of internal Hom complexes induced by an isomorphism of sources. -/
def homMapIsoOfIso {E E' : CochainComplex (SheafOfModules.{w} (ringSheaf X.O)) ℤ}
    (e : E ≅ E') : (sheafHomComplex X E' L).obj ≅ (sheafHomComplex X E L).obj where
  hom := homMap X e.hom (𝟙 L)
  inv := homMap X e.inv (𝟙 L)
  hom_inv_id := by rw [homMap_comp, e.inv_hom_id, Category.comp_id, homMap_id]
  inv_hom_id := by rw [homMap_comp, e.hom_inv_id, Category.comp_id, homMap_id]

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The coherence of the cohomology of the internal Hom complex depends only on the source up
to isomorphism. -/
theorem HomHomologyCoherent.of_iso {E E' : CochainComplex (SheafOfModules.{w} (ringSheaf X.O)) ℤ}
    (e : E ≅ E') (h : HomHomologyCoherent X L E') : HomHomologyCoherent X L E := fun j =>
  Stacks.SheafOfModules.isCoherentOnSite_of_iso
    ((HomologicalComplex.homologyFunctor _ _ j).mapIso (homMapIsoOfIso (L := L) e)) (h j)

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A retract of the source passes to a retract of the cohomology of the internal Hom
complex. -/
theorem HomHomologyCoherent.of_retract
    {E E' : CochainComplex (SheafOfModules.{w} (ringSheaf X.O)) ℤ}
    (ρ : Retract E E') (h : HomHomologyCoherent X L E') : HomHomologyCoherent X L E := fun j =>
  Stacks.SheafOfModules.isCoherentOnSite_of_retract
    ⟨HomologicalComplex.homologyMap (homMap X ρ.r (𝟙 L)) j,
      HomologicalComplex.homologyMap (homMap X ρ.i (𝟙 L)) j, by
        rw [← HomologicalComplex.homologyMap_comp, homMap_comp, ρ.retract, Category.comp_id,
          homMap_id, HomologicalComplex.homologyMap_id]⟩ (h j)

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A zero source has an internal Hom complex with coherent (zero) cohomology. -/
theorem HomHomologyCoherent.of_isZero
    {E : CochainComplex (SheafOfModules.{w} (ringSheaf X.O)) ℤ} (hE : IsZero E) :
    HomHomologyCoherent X L E := fun j =>
  Stacks.SheafOfModules.isCoherentOnSite_zero
    ((HomologicalComplex.homologyFunctor _ _ j).map_isZero
      (sheafHomComplex_isZero_of_isZero X hE L))

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Two out of three for a termwise split short complex of sources.** If the outer sources
have internal Hom complexes with coherent cohomology, so does the middle one: the internal Hom
complexes form a short exact sequence, and its long exact cohomology sequence has the middle
cohomology sheaf flanked by four coherent ones. -/
theorem HomHomologyCoherent.of_degreewiseSplit
    (S : ShortComplex (CochainComplex (SheafOfModules.{w} (ringSheaf X.O)) ℤ))
    (σ : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).Splitting)
    (h₁ : HomHomologyCoherent X L S.X₁) (h₃ : HomHomologyCoherent X L S.X₃) :
    HomHomologyCoherent X L S.X₂ := by
  intro j
  have hT := internalHomShortComplex_shortExact X S L σ
  exact Stacks.SheafOfModules.isCoherentOnSite_of_exact₅ _ _ _
    (hT.homology_exact₁ (j - 1) j (by simp)) (hT.homology_exact₂ j)
    (hT.homology_exact₃ j (j + 1) (by simp))
    (h₁ (j - 1)) (h₃ j) (h₁ j) (h₃ (j + 1))

/-- **The unit source.** For a source concentrated in degree `k` with that term the structure
sheaf, the internal Hom complex is, on three-term truncations, the universe lift of `L` shifted
by `k`; the universe lift is exact and preserves coherence. -/
theorem HomHomologyCoherent.single_unit
    (hL : ∀ q, SheafOfModules.IsCoherentOnSite (L.homology q)) (k : ℤ) :
    HomHomologyCoherent X L ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj
      (SheafOfModules.unit (ringSheaf X.O))) := by
  intro j
  let E := (HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj
    (SheafOfModules.unit (ringSheaf X.O))
  let G := SheafOfModules.uliftForPresentationFunctor.{u, v, w, w, max u v w}
    (R := ringSheaf X.O)
  have : PreservesFiniteLimits G :=
    SheafOfModules.preservesFiniteLimits_uliftForPresentationFunctor (ringSheaf X.O)
  have : PreservesFiniteColimits G :=
    SheafOfModules.preservesFiniteColimits_uliftForPresentationFunctor.{u, v, w, w, max u v w}
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  let e₁ := (sheafHomComplex X E L).obj.homologyIsoSc' (j - 1) j (j + 1) (by simp) (by simp)
  let e₂ := ShortComplex.homologyMapIso (homUnitShortComplexIso X (F := L) k (j - 1) j (j + 1)
    (by omega) rfl (HomologicalComplex.singleObjXSelf _ k _)
    (HomologicalComplex.single_obj_d (c := ComplexShape.up ℤ) k _ k (k + 1))
    (fun p hp => HomologicalComplex.isZero_single_obj_X _ _ _ p hp))
  let e₃ := (L.sc' (k + (j - 1)) (k + j) (k + (j + 1))).mapHomologyIso G
  let e₄ := G.mapIso (L.homologyIsoSc' (k + (j - 1)) (k + j) (k + (j + 1))
    (by simp; omega) (by simp; omega)).symm
  exact Stacks.SheafOfModules.isCoherentOnSite_of_iso (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄).symm
    (SheafOfModules.isCoherentOnSite_uliftForPresentation _ (hL (k + j)))

/-- Sheaves of modules on a ringed site have finite biproducts, being abelian. -/
local instance hasFiniteBiproducts_sheafOfModules :
    HasFiniteBiproducts (SheafOfModules.{w} (ringSheaf X.O)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **A binary biproduct in one degree.** The split short complex `A ⟶ A ⊞ B ⟶ B`, placed in
degree `k`, is termwise split, so two out of three applies. -/
theorem HomHomologyCoherent.single_biprod (k : ℤ)
    (A B : SheafOfModules.{w} (ringSheaf X.O))
    (hA : HomHomologyCoherent X L ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj A))
    (hB : HomHomologyCoherent X L ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj B)) :
    HomHomologyCoherent X L ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj (A ⊞ B)) := by
  let Sg := HomologicalComplex.single (SheafOfModules.{w} (ringSheaf X.O)) (ComplexShape.up ℤ) k
  let T := (ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B) biprod.snd (by simp)).map Sg
  exact HomHomologyCoherent.of_degreewiseSplit T
    (fun p => ((ShortComplex.Splitting.ofHasBinaryBiproduct A B).map Sg).map _) hA hB

/-- **A finite free module in one degree.** By induction on the rank, through the splittings
`O^{⊕(r+1)} ≅ O^{⊕r} ⊞ O`. -/
theorem HomHomologyCoherent.single_biproduct_unit
    (hL : ∀ q, SheafOfModules.IsCoherentOnSite (L.homology q)) (k : ℤ) (r : ℕ) :
    HomHomologyCoherent X L ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj
      (⨁ fun _ : Fin r => SheafOfModules.unit (ringSheaf X.O))) := by
  let Sg := HomologicalComplex.single (SheafOfModules.{w} (ringSheaf X.O)) (ComplexShape.up ℤ) k
  induction r with
  | zero =>
    exact HomHomologyCoherent.of_isZero
      (Sg.map_isZero (isZero_biproduct_fin_zero (SheafOfModules.unit (ringSheaf X.O))))
  | succ r ih =>
    exact HomHomologyCoherent.of_iso
      (Sg.mapIso (biproductFinSuccIso (SheafOfModules.unit (ringSheaf X.O)) r))
      (HomHomologyCoherent.single_biprod k _ _ ih (HomHomologyCoherent.single_unit hL k))

/-- **A direct summand of a finite free module in one degree.** It is a retract of a finite
free module, which is a finite biproduct of copies of the structure sheaf. -/
theorem HomHomologyCoherent.single_of_isDirectSummandOfFiniteFree
    (hL : ∀ q, SheafOfModules.IsCoherentOnSite (L.homology q)) (k : ℤ)
    {Q : SheafOfModules.{w} (ringSheaf X.O)}
    (hQ : _root_.IsDirectSummandOfFiniteFree (ringSheaf X.O) Q) :
    HomHomologyCoherent X L ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj Q) := by
  obtain ⟨n, i, r, hir⟩ :=
    (_root_.isDirectSummandOfFiniteFree_iff_free (ringSheaf X.O) Q).1 hQ
  let hfree : SheafOfModules.free (R := ringSheaf X.O) (ULift.{w} (Fin n)) ≅
      ⨁ fun _ : Fin n => SheafOfModules.unit (ringSheaf X.O) :=
    (IsColimit.coconePointUniqueUpToIso
        (SheafOfModules.isColimitFreeCofan (R := ringSheaf X.O) (ULift.{w} (Fin n)))
        (biproduct.isColimit fun _ : ULift.{w} (Fin n) =>
          SheafOfModules.unit (ringSheaf X.O))).trans
      (biproduct.whiskerEquiv
        (f := fun _ : ULift.{w} (Fin n) => SheafOfModules.unit (ringSheaf X.O))
        (g := fun _ : Fin n => SheafOfModules.unit (ringSheaf X.O)) Equiv.ulift
        fun _ => Iso.refl _)
  let Sg := HomologicalComplex.single (SheafOfModules.{w} (ringSheaf X.O)) (ComplexShape.up ℤ) k
  let ρ : Retract Q (⨁ fun _ : Fin n => SheafOfModules.unit (ringSheaf X.O)) :=
    ⟨i ≫ hfree.hom, hfree.inv ≫ r, by
      rw [Category.assoc, ← Category.assoc hfree.hom, hfree.hom_inv_id, Category.id_comp, hir]⟩
  exact HomHomologyCoherent.of_retract (ρ.map Sg)
    (HomHomologyCoherent.single_biproduct_unit hL k n)

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- A zero module is a direct summand of a finite free module. -/
theorem isDirectSummandOfFiniteFree_of_isZero {Q : SheafOfModules.{w} (ringSheaf X.O)}
    (hQ : IsZero Q) : _root_.IsDirectSummandOfFiniteFree (ringSheaf X.O) Q :=
  (_root_.isDirectSummandOfFiniteFree_iff_free (ringSheaf X.O) Q).2
    ⟨0, 0, 0, hQ.eq_of_src _ _⟩

/-- **The bounded case.** If `E` vanishes outside the window `[a, a + r)` and each of its terms
is a direct summand of a finite free module, the internal Hom complex out of `E` has coherent
cohomology. The lowest term is split off by `bottomProjection`, whose kernel has a shorter
window. -/
theorem HomHomologyCoherent.of_bounded
    (hL : ∀ q, SheafOfModules.IsCoherentOnSite (L.homology q)) (r : ℕ) (a : ℤ)
    (E : CochainComplex (SheafOfModules.{w} (ringSheaf X.O)) ℤ)
    (hlo : ∀ i, i < a → IsZero (E.X i)) (hhi : ∀ i, a + r ≤ i → IsZero (E.X i))
    (hterm : ∀ i, _root_.IsDirectSummandOfFiniteFree (ringSheaf X.O) (E.X i)) :
    HomHomologyCoherent X L E := by
  induction r generalizing a E with
  | zero =>
    exact HomHomologyCoherent.of_isZero (complex_isZero_of_terms E fun i =>
      (lt_or_ge i a).elim (hlo i) fun hi => hhi i (by push_cast; omega))
  | succ r ih =>
    have ha : IsZero (E.X (a - 1)) := hlo (a - 1) (by omega)
    set p := bottomProjection E a ha
    set K := kernel p
    have hz : IsZero (K.X a) := isZero_kernel_bottomProjection_X_self E a ha
    have eK (i : ℤ) (hi : i ≠ a) : K.X i ≅ E.X i :=
      have := isIso_kernel_ι_bottomProjection_f E a ha i hi
      asIso ((kernel.ι p).f i)
    have hKterm (i : ℤ) : _root_.IsDirectSummandOfFiniteFree (ringSheaf X.O) (K.X i) := by
      by_cases hi : i = a
      · subst i
        exact isDirectSummandOfFiniteFree_of_isZero hz
      · exact _root_.IsDirectSummandOfFiniteFree.of_iso (ringSheaf X.O) (eK i hi) (hterm i)
    have hKlo (i : ℤ) (hi : i < a + 1) : IsZero (K.X i) :=
      if hia : i = a then hia ▸ hz else (hlo i (by omega)).of_iso (eK i hia)
    have hKhi (i : ℤ) (hi : a + 1 + r ≤ i) : IsZero (K.X i) :=
      (hhi i (by push_cast; omega)).of_iso (eK i (by omega))
    have hAq : HomHomologyCoherent X L
        ((HomologicalComplex.single (SheafOfModules.{w} (ringSheaf X.O))
          (ComplexShape.up ℤ) a).obj (E.X a)) :=
      HomHomologyCoherent.single_of_isDirectSummandOfFiniteFree hL a (hterm a)
    refine HomHomologyCoherent.of_degreewiseSplit
      (ShortComplex.mk (kernel.ι p) p (kernel.condition p)) (fun i => ?_)
      (ih (a + 1) K hKlo hKhi hKterm) hAq
    by_cases hi : i = a
    · subst i
      exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hz (isIso_bottomProjection_f_self E a ha)
    · exact ShortComplex.Splitting.ofIsIsoOfIsZero _
        (isIso_kernel_ι_bottomProjection_f E a ha i hi)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (E.X a) i hi)

/-- **The cohomology of the internal Hom complex out of a strictly perfect complex into a complex
with coherent cohomology is coherent.**

`P` is strictly perfect in the sense of Stacks 08FL and every cohomology sheaf of `L` is
coherent. Nothing else is assumed: neither coherence of the structure sheaf nor any property of
`L` beyond the coherence of its cohomology. -/
theorem isCoherentOnSite_homology_sheafHomComplex_of_isStrictlyPerfect
    (P : CochainComplex (SheafOfModules.{w} (ringSheaf X.O)) ℤ)
    (hP : _root_.IsStrictlyPerfect (ringSheaf X.O) P)
    (hL : ∀ q, SheafOfModules.IsCoherentOnSite (L.homology q)) (j : ℤ) :
    SheafOfModules.IsCoherentOnSite ((sheafHomComplex X P L).obj.homology j) := by
  obtain ⟨a, ha⟩ := hP.bounded.bddBelow
  obtain ⟨b, hb⟩ := hP.bounded.bddAbove
  refine HomHomologyCoherent.of_bounded hL (b - a + 1).toNat a P ?_ ?_ hP.termDirectSummand j <;>
  · intro i hi
    by_contra hz
    have := ha hz
    have := hb hz
    omega

end AlgebraicGeometry.RingedSite.Raised

/-! ### Comparison along a strictly perfect approximation -/

namespace AlgebraicGeometry.RingedSite.Raised

variable (Y : RingedSite.{c, u, u}) [EssentiallySmall.{u} Y.C]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{max c u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}]

/-- **The internal Hom complex out of a cohomologically bounded-above complex into a strictly
bounded-below K-injective complex has no cohomology below the difference of the bounds.** If
`C'` has no cohomology above `d` and `J'` is K-injective and concentrated in degrees `≥ b`, then
`Hⁿ(SheafHom(C', J')) = 0` for `n < b - d`.

The canonical truncation `τ_{≤ d} C' ⟶ C'` is a quasi-isomorphism, so by Stacks 0A95 it induces
a quasi-isomorphism of internal Hom complexes into `J'`, and `SheafHom(τ_{≤ d} C', J')` is
concentrated in degrees `≥ b - d` on the nose. -/
theorem isZero_homology_sheafHomComplex_of_isLE
    (C' J' : CochainComplex (SheafOfModules.{u} (ringSheaf Y.O)) ℤ) (d b : ℤ)
    [C'.IsLE d] [J'.IsKInjective] [J'.IsStrictlyGE b] (n : ℤ) (hn : n < b - d) :
    IsZero ((sheafHomComplex Y C' J').obj.homology n) := by
  have hq : QuasiIso (homMap Y (C'.ιTruncLE d) (𝟙 J')) :=
    homMap_quasiIso Y (𝟙 J') (C'.ιTruncLE d)
  have := isStrictlyGE_sheafHomComplex Y (C'.truncLE d) J' d b
  have h0 : IsZero ((sheafHomComplex Y (C'.truncLE d) J').obj.homology n) :=
    ((sheafHomComplex Y (C'.truncLE d) J').obj.exactAt_of_isGE (b - d) n hn).isZero_homology
  exact IsZero.of_iso h0 (asIso (HomologicalComplex.homologyMap
    (homMap Y (C'.ιTruncLE d) (𝟙 J')) n))

/-- **Comparison of the internal Hom complex along an approximation with acyclic cone in high
degrees.** Let `α : P ⟶ A'` be a morphism of complexes whose mapping cone has no cohomology in
degrees `≥ m`, and let `J'` be K-injective and concentrated in degrees `≥ b`. Then for
`n + 1 ≤ b - m`

`Hⁿ(SheafHom(A', J')) ≅ Hⁿ⁺¹(SheafHom(P[1], J'))`.

The rotated cone triangle `A' ⟶ C(α) ⟶ P[1]` is termwise split, so the internal Hom complexes
into `J'` form a short exact sequence, and the cohomology of `SheafHom(C(α), J')` vanishes in the
two degrees which flank the connecting morphism, by
`AlgebraicGeometry.RingedSite.Raised.isZero_homology_sheafHomComplex_of_isLE`. -/
def sheafHomComplexHomologyIsoOfApproximation
    {P A' : CochainComplex (SheafOfModules.{u} (ringSheaf Y.O)) ℤ} (α : P ⟶ A')
    (J' : CochainComplex (SheafOfModules.{u} (ringSheaf Y.O)) ℤ) (m b n : ℤ)
    (hcone : ∀ i, m ≤ i → IsZero ((CochainComplex.mappingCone α).homology i))
    [J'.IsKInjective] [J'.IsStrictlyGE b] (hn : n + 1 ≤ b - m) :
    (sheafHomComplex Y A' J').obj.homology n ≅
      (sheafHomComplex Y (P⟦(1 : ℤ)⟧) J').obj.homology (n + 1) := by
  have : (CochainComplex.mappingCone α).IsLE (m - 1) := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (hcone i (by omega))
  exact (internalHomShortComplex_shortExact Y
    (CochainComplex.mappingCone.triangleRotateShortComplex α) J'
    (CochainComplex.mappingCone.triangleRotateShortComplexSplitting α)).δIso n (n + 1) (by simp)
    (isZero_homology_sheafHomComplex_of_isLE Y (CochainComplex.mappingCone α) J' (m - 1) b n
      (by omega))
    (isZero_homology_sheafHomComplex_of_isLE Y (CochainComplex.mappingCone α) J' (m - 1) b
      (n + 1) (by omega))

/-- **Coherence of the cohomology of the internal Hom complex out of a complex with a strictly
perfect approximation.** Let `α : P ⟶ A'` be a morphism from a strictly perfect complex whose
mapping cone has no cohomology in degrees `≥ m`, and let `J'` be a K-injective complex
concentrated in degrees `≥ b` with coherent cohomology sheaves. Then
`Hⁿ(SheafHom(A', J'))` is coherent for every `n` with `n + 1 ≤ b - m`. -/
theorem isCoherentOnSite_homology_sheafHomComplex_of_approximation
    {P A' : CochainComplex (SheafOfModules.{u} (ringSheaf Y.O)) ℤ}
    (hP : _root_.IsStrictlyPerfect (ringSheaf Y.O) P) (α : P ⟶ A')
    (J' : CochainComplex (SheafOfModules.{u} (ringSheaf Y.O)) ℤ) (m b n : ℤ)
    (hcone : ∀ i, m ≤ i → IsZero ((CochainComplex.mappingCone α).homology i))
    [J'.IsKInjective] [J'.IsStrictlyGE b]
    (hJ : ∀ q, SheafOfModules.IsCoherentOnSite (J'.homology q)) (hn : n + 1 ≤ b - m) :
    SheafOfModules.IsCoherentOnSite ((sheafHomComplex Y A' J').obj.homology n) :=
  Stacks.SheafOfModules.isCoherentOnSite_of_iso
    (sheafHomComplexHomologyIsoOfApproximation Y α J' m b n hcone hn).symm
    (isCoherentOnSite_homology_sheafHomComplex_of_isStrictlyPerfect (P⟦(1 : ℤ)⟧)
      (SheafOfModules.isStrictlyPerfect_shift (ringSheaf Y.O) hP 1) hJ (n + 1))

end AlgebraicGeometry.RingedSite.Raised

end
