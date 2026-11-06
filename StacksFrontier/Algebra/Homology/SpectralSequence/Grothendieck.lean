module

public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.WeakSerreClassRightDerivedFunctorPlus
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Grothendieck spectral sequence

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors between abelian categories, with `𝒜` and
`ℬ` having enough injectives, and assume that `F` carries injective objects of `𝒜` to objects
that are right acyclic for `G`; by [Stacks, Tag 015M] this is equivalent to the canonical map
`R(G ∘ F) ⟶ RG ∘ RF` being an isomorphism. For every object `X` of `D⁺(𝒜)` there is a
spectral sequence `(E_r, d_r)_{r ≥ 0}` of `𝒞`, with `d_r` of bidegree `(r, -r + 1)`, such that
```
E_2^{p,q} = R^pG(H^q(RF(X))),
```
which is bounded, converges to `H^*(R(G ∘ F)(X))`, and induces a finite filtration on each
`H^n(R(G ∘ F)(X))`.

Here a spectral sequence converging to `H^*(K)` is presented by a filtered complex `K`: its
pages are identified with the quotients `Z_r^{p,q}/D_r^{p,q}` of [Stacks, Tag 012M], and
boundedness, finiteness of the filtration `F^pH^n(K)` induced on cohomology and convergence
(regularity, `d_r = 0` for `r ≫ 0`, and the equalities (012S) and (012T) for the stable cycles
and boundaries) are properties of that presentation. The subobjects `F^pK^n`, `Z_r^{p,q}`,
`D_r^{p,q}` and `F^pH^n(K)` are quantified together with their defining equations, as in
[Stacks, Tag 012W].

## Main results

* `CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`: the
  Grothendieck spectral sequence `R^pG(H^q(RF(X))) ⇒ H^{p+q}(R(G ∘ F)(X))`.

## References

* [Stacks, Tag 015N]
* [Stacks, Tag 015M]
* [Stacks, Tag 015J]
* [Stacks, Tag 0130]
* [Stacks, Tag 0132]
-/

public section

universe w w' w'' v v' v'' u u' u''

open CategoryTheory Limits Opposite

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w''} C]

/-- The Grothendieck spectral sequence. Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors
between abelian categories, with `𝒜` and `ℬ` having enough injectives, such that `F(I)` is right
acyclic for `G` for every injective object `I` of `𝒜`, and let `X` be an object of `D⁺(𝒜)`.
There is a filtered complex `K` of `𝒞` with `H^n(K) ≅ H^n(R(G ∘ F)(X))` for all `n`, whose
filtration is finite in each degree and whose spectral sequence `E`, presented by its pages
`Z_r^{p,q}/D_r^{p,q}`, has `E_2^{p,q} ≅ R^pG(H^q(RF(X)))`, is bounded, induces a finite
filtration on each `H^n(K)`, and converges to `H^*(K)`. -/
@[stacks 015N,
  sga "4 V 0.3" "(ii) ⇒ (i)",
  sga "4 VII 1.5" "more general",
  sga "4½ Arcata 2.3.3" "more general",
  sga "4½ Arcata 2.3.4" "more general"]
theorem exists_spectralSequence_rightDerivedFunctorPlus_comp (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [EnoughInjectives A] [EnoughInjectives B]
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) (X : DerivedCategory.Plus A) :
    ∃ K : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ,
      (∀ n : ℤ, Nonempty (K.X.homology n ≅
        (DerivedCategory.Plus.homologyFunctor C n).obj
          ((F ⋙ G).rightDerivedFunctorPlus.obj X))) ∧
      K.filtration.IsDegreewiseFinite ∧
      ∀ (Fil : ∀ (_p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ p n : ℤ, Fil p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
        (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, Z r p n =
          Fil p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (Fil (p + r) (n + 1)))
        (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
        (FH : ∀ (n _p : ℤ), Subobject (K.X.homology n))
        (_ : ∀ n p : ℤ, FH n p =
          imageSubobject (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)),
      ∃ (E : CohomologicalSpectralSequence C 0)
        (_ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))),
        (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
          (G.rightDerivedPlus p).obj
            ((DerivedCategory.Plus.homologyFunctor B q).obj (F.rightDerivedFunctorPlus.obj X)))) ∧
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0).X (p, n - p))}.Finite) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
        (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
          (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
        (∀ p n : ℤ,
          IsGLB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) ⊔
                Fil (p + 1) n)
            (kernelSubobject (K.X.d n (n + 1)) ⊓ Fil p n ⊔ Fil (p + 1) n) ∧
          IsLUB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (Fil (p - r) (n - 1)) ⊔
                Fil (p + 1) n)
            (imageSubobject (K.X.d (n - 1) n) ⊓ Fil p n ⊔ Fil (p + 1) n)) := by
  let β := whiskerRight (mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
      DerivedCategory.Plus.Qh ≫
    whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnith ≫
    whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus
  let t := (F ⋙ G).rightDerivedFunctorPlus.rightDerivedDesc
    (F ⋙ G).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A)
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) β
  have ht : (F ⋙ G).rightDerivedFunctorPlusUnith ≫ whiskerLeft DerivedCategory.Plus.Qh t = β :=
    Functor.rightDerived_fac _ _ _ _ _
  have : IsIso t := (isIso_iff_rightAcyclic_obj_injective F G t ht).2 hFG
  obtain ⟨M, ⟨eM⟩⟩ :=
    DerivedCategory.Plus.exists_iso_Q_obj (F.rightDerivedFunctorPlus.obj X)
  obtain ⟨n₀, hn₀⟩ := M.property
  obtain ⟨I, hI⟩ := M.obj.exists_cartanEilenbergResolution n₀
  let L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.bicomplex
  have hq : ∀ p q, q < 0 → IsZero ((L.X p).X q) := fun p q hq =>
    G.map_isZero (CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X p) 0 q hq)
  have hp : ∀ p, p < n₀ → IsZero (L.X p) := fun p hp =>
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE I.bicomplex n₀ p hp)
  have hfin := StacksDraft.TotalComplexQuasiIso.finite_not_isZero_of_bounded L n₀ hq hp
  have : L.HasTotal (ComplexShape.up ℤ) :=
    StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded L n₀ hq hp
  obtain ⟨-, h2, h3⟩ := I.exists_homologyIso_rightDerivedPlus G M.property
  have eH : ∀ q : ℤ, M.obj.homology q ≅
      (DerivedCategory.Plus.homologyFunctor B q).obj (F.rightDerivedFunctorPlus.obj X) :=
    fun q => ((DerivedCategory.homologyFunctorFactors B q).app M.obj).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor B q).mapIso eM
  refine ⟨L.totalFiltration₂, fun n => ?_, L.isDegreewiseFinite_totalFiltration₂ hfin,
    fun Fil hFil Z hZ D hD FH hFH => ?_⟩
  · obtain ⟨e⟩ := h3 n
    exact ⟨e ≪≫ (DerivedCategory.Plus.homologyFunctor C n).mapIso
      (G.rightDerivedFunctorPlus.mapIso eM ≪≫ (asIso (t.app X)).symm)⟩
  · obtain ⟨E, e, -, hδ, -, -, -⟩ :=
      CochainComplex.exists_cohomologicalSpectralSequence L.totalFiltration₂ Fil hFil Z hZ D hD
    obtain ⟨-, -, hE2⟩ := L.exists_iso_pages_totalFiltration₂ Fil hFil Z hZ D hD E e hδ
    obtain ⟨c₁, c₂, c₃, c₄, -⟩ :=
      L.isBounded_and_converges_totalFiltration₂ hfin Fil hFil Z hZ D hD FH hFH E e
    refine ⟨E, e, fun p q => ?_, c₁, c₂, c₃, c₄⟩
    obtain ⟨e₂⟩ := hE2 p q
    obtain ⟨e₂'⟩ := h2 p q
    exact ⟨e₂ ≪≫ e₂' ≪≫ (G.rightDerivedPlus p).mapIso (eH q)⟩

end CategoryTheory.Functor

end
