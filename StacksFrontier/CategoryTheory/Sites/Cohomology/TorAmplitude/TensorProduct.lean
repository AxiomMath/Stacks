module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18.FlatTensorProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.TensorProduct
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Tor amplitudes add under the derived tensor product, on a ringed site

Let `(C, O)` be a ringed site and let `T` be a derived tensor product on `D(O)`. If `K` has Tor
amplitude in `[a, b]` and `L` has Tor amplitude in `[c, d]`, then `K ⊗^L_O L` has Tor amplitude
in `[a + c, b + d]`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_tensor`: **Stacks 09JA.** Tor
  amplitude bounds add under the derived tensor product.
* `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_total`: every term of the total complex of
  a double complex of flat `O`-modules is flat.

## Implementation notes

The source's hint is the spectral sequence for Tors; the argument used here is the one the
library is already set up for, and is the ringed-site form of the ringed-space proof in
`StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/TensorProduct.lean`. Both factors are
replaced by bounded flat representatives `A` and `B` using Stacks 08G1, which are K-flat by
Stacks 06YQ, so the derived tensor product is the total complex `Tot(A ⊗_O B)`. That total
complex is again a bounded flat representative: its terms are direct sums of the
`A^p ⊗_O B^q`, flat by Stacks 0G6Q and Stacks 05NG, and the summands contributing to a degree
`i ∉ [a + c, b + d]` all have `p ∉ [a, b]` or `q ∉ [c, d]`, hence vanish. Stacks 08G1 read in
the easy direction concludes.

The direct sums indexing the terms of a total complex are indexed by a subtype of `ℤ × ℤ`,
which lives in `Type 0`, whereas the direct-sum clause of Stacks 05NG is stated for an index
type in the universe of the sections; `isFlat_coproduct_of_smallIndex` reindexes along
`Equiv.ulift`, which is the only reason it exists.

The two site universes `u` and `v` and the derived category's own hom universe `d` stay
independent, but the sections of the structure sheaf and of the modules live in `max u v`: the
direction of Stacks 08G1 producing the representative is available only there, because it reads
Tor amplitude of the object itself off the unit law for the derived tensor product. See the
implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/FlatRepresentative.lean`.

The statement carries no hypothesis `a ≤ b` or `c ≤ d`. For a degenerate interval Tor amplitude
in `[a, b]` says that *every* cohomology sheaf of every derived tensor product vanishes, which
is stronger than Tor amplitude in any one-point interval, so the general case reduces to the
ordered one by shrinking the degenerate interval to a point chosen below the degree under
consideration.

## References

* [Stacks Project, Tag 09JA](https://stacks.math.columbia.edu/tag/09JA)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 0G6Q](https://stacks.math.columbia.edu/tag/0G6Q)
* [Stacks Project, Tag 05NG](https://stacks.math.columbia.edu/tag/05NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

section Flatness

variable {Y : RingedSite.{u, v, max u v}}
  [HasSheafify Y.J AddCommGrpCat.{max u v}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **A direct sum of flat `O`-modules indexed by a type in the lowest universe is flat.** This
is the direct-sum clause of Stacks 05NG after reindexing along `Equiv.ulift`; the statement
there has the index type in the universe of the sections, while the direct sums appearing in a
total complex are indexed by a subtype of `ℤ × ℤ`. -/
theorem isFlat_coproduct_of_smallIndex {ι : Type}
    (F : ι → RingedSite.Modules.{u, v, max u v} Y) [HasCoproduct F]
    (hF : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v}
      (O := Y.O) (F i)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O) (∐ F) := by
  let G : ULift.{max u v} ι → RingedSite.Modules.{u, v, max u v} Y := fun i => F i.down
  let _ : HasCoproduct G :=
    hasCoproduct_of_equiv_of_iso F G Equiv.ulift (fun _ => Iso.refl _)
  refine Stacks.SheafOfModules.FlatRetract.isFlat_of_iso Y.O (M := ∐ G) ?_
    (Stacks.SheafOfModules.FlatColimits.isFlat_coproduct (O := Y.O) G (fun i => hF i.down))
  exact
    { hom := Sigma.desc fun i => Sigma.ι F i.down
      inv := Sigma.desc fun i => Sigma.ι G (ULift.up i)
      hom_inv_id := by apply colimit.hom_ext; rintro ⟨i⟩; simp [G]
      inv_hom_id := by apply colimit.hom_ext; rintro ⟨i⟩; simp [G] }

/-- **Every term of the total complex of a double complex of flat `O`-modules is flat.** The
term in degree `i` is the direct sum of the terms `Z^{p, q}` with `p + q = i`. -/
theorem isFlat_total
    (Z : HomologicalComplex₂ (RingedSite.Modules.{u, v, max u v} Y)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [Z.HasTotal (ComplexShape.up ℤ)]
    (hflat : ∀ p q, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v}
      (O := Y.O) ((Z.X p).X q))
    (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O)
      ((Z.total (ComplexShape.up ℤ)).X i) :=
  isFlat_coproduct_of_smallIndex _ (fun j => hflat j.val.1 j.val.2)

end Flatness

section Derived

variable {Y : RingedSite.{u, v, max u v}}
  [HasSheafify Y.J AddCommGrpCat.{max u v}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, max u v} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).obj
    M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, max u v} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

variable (T : DerivedTensorProduct.{u, v, max u v, d} Y)
  (K L : RingedSite.DerivedModules.{u, v, max u v, d} Y)

/-- **Stacks 09JA for ordered intervals.** The derived tensor product of an object of Tor
amplitude in `[a, b]` with an object of Tor amplitude in `[c, d]` has Tor amplitude in
`[a + c, b + d]`. -/
theorem hasTorAmplitude_tensor_of_le (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (hK : HasTorAmplitude T K a b) (hL : HasTorAmplitude T L c d) :
    HasTorAmplitude T ((T.tensor.obj K).obj L) (a + c) (b + d) := by
  classical
  obtain ⟨A, hAflat, hAzero, ⟨eA⟩⟩ :=
    exists_flatRepresentative_of_hasTorAmplitude T K a b hab hK
  obtain ⟨B, hBflat, hBzero, ⟨eB⟩⟩ :=
    exists_flatRepresentative_of_hasTorAmplitude T L c d hcd hL
  have hALE : A.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hAzero i (by simp only [Set.mem_Icc]; omega)
  have hBLE : B.IsStrictlyLE d := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hBzero i (by simp only [Set.mem_Icc]; omega)
  have hAkflat := Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat Y.O A ⟨b, hALE⟩ hAflat
  have hBkflat := Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat Y.O B ⟨d, hBLE⟩ hBflat
  let Z : HomologicalComplex₂ (RingedSite.Modules.{u, v, max u v} Y)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj A).obj B
  have htermflat : ∀ p q, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v}
      (O := Y.O) ((Z.X p).X q) := fun p q =>
    Stacks.SheafOfModules.FlatTensor.isFlat_tensor (A.X p) (B.X q) (hAflat p) (hBflat q)
  have hZzero : ∀ p q, p ∉ Set.Icc a b ∨ q ∉ Set.Icc c d → IsZero ((Z.X p).X q) := by
    rintro p q (hp | hq)
    · exact Functor.map_isZero
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj (B.X q)) (hAzero p hp)
    · exact Functor.map_isZero
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (A.X p)) (hBzero q hq)
  refine hasTorAmplitude_of_flatRepresentative T _ (a + c) (b + d)
    (Z.total (ComplexShape.up ℤ)) (isFlat_total Z htermflat)
    (fun i hi => Stacks.Cohomology.TorAmplitude.Tensor.isZero_total_X_of_support
      Z a b c d i hZzero hi) ?_
  exact (T.comparison A B hAkflat hBkflat).symm ≪≫
    ((T.tensor.mapIso eA).app (DerivedCategory.Q.obj B)) ≪≫
    ((T.tensor.obj K).mapIso eB)

/-- **Stacks 09JA.** If `K` has Tor amplitude in `[a, b]` and `L` has Tor amplitude in
`[c, d]`, then `K ⊗^L_O L` has Tor amplitude in `[a + c, b + d]`.

A degenerate interval is replaced by a one-point interval chosen below the degree under
consideration, which is a weaker hypothesis, and `hasTorAmplitude_tensor_of_le` applies. -/
@[stacks 09JA]
theorem hasTorAmplitude_tensor (a b c d : ℤ)
    (hK : HasTorAmplitude T K a b) (hL : HasTorAmplitude T L c d) :
    HasTorAmplitude T ((T.tensor.obj K).obj L) (a + c) (b + d) := by
  by_cases hab : a ≤ b
  · by_cases hcd : c ≤ d
    · exact hasTorAmplitude_tensor_of_le T K L a b c d hab hcd hK hL
    · intro F i hi
      have hL' : HasTorAmplitude T L (i - b - 1) (i - b - 1) :=
        fun G j hj => hL G j (by simp only [Set.mem_Icc]; omega)
      exact hasTorAmplitude_tensor_of_le T K L a b (i - b - 1) (i - b - 1) hab le_rfl
        hK hL' F i (by simp only [Set.mem_Icc]; omega)
  · intro F i hi
    have hK' : HasTorAmplitude T K (i - d - 1) (i - d - 1) :=
      fun G j hj => hK G j (by simp only [Set.mem_Icc]; omega)
    by_cases hcd : c ≤ d
    · exact hasTorAmplitude_tensor_of_le T K L (i - d - 1) (i - d - 1) c d le_rfl hcd
        hK' hL F i (by simp only [Set.mem_Icc]; omega)
    · have hL' : HasTorAmplitude T L 0 0 :=
        fun G j hj => hL G j (by simp only [Set.mem_Icc]; omega)
      have hK'' : HasTorAmplitude T K (i + 1) (i + 1) :=
        fun G j hj => hK G j (by simp only [Set.mem_Icc]; omega)
      exact hasTorAmplitude_tensor_of_le T K L (i + 1) (i + 1) 0 0 le_rfl le_rfl
        hK'' hL' F i (by simp only [Set.mem_Icc]; omega)

end Derived

end Stacks.SheafOfModules.DerivedTensorProduct

end
