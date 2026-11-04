module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.ExactSequence
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Functor

/-!
# Naturality of the determinant map of a short exact sequence

An isomorphism between two short exact sequences of finite-length modules commutes with the
canonical determinant maps of the two sequences.

## Main results

* `Module.FiniteLength.determinantExactSequenceMap_natural` states naturality of the
  determinant map for isomorphisms of short exact sequences.

## Implementation notes

Finite-length modules and their isomorphisms are objects and morphisms of the groupoid
`Module.FiniteLength.FiniteLengthModuleIso`. The three isomorphisms are required to commute
with both maps of the short exact sequences. The determinant maps on isomorphisms are the
`mapLinearEquiv` component of the determinant functor of Tag 05M7. Since the determinant
map of an exact sequence is pinned down by its values on tensors of symbols, naturality is
checked there, where it reduces to the fact that an isomorphism of sequences takes a
concatenation to a concatenation.

## References

* [Stacks Project, Tag 02PA](https://stacks.math.columbia.edu/tag/02PA)
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct
namespace Module.FiniteLength

universe u v

/-- An isomorphism of short exact sequences commutes with the determinant maps on tensors of
symbols, because it carries a concatenation of an admissible sequence with lifts to another
such concatenation. -/
private theorem determinantExactSequenceMap_natural_on_symbols
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K L M K' L' M' : FiniteLengthModuleIso.{u, v} R}
    (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
    (i' : K'.of.obj →ₗ[R] L'.of.obj) (p' : L'.of.obj →ₗ[R] M'.of.obj)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (hi' : Function.Injective i') (hp' : Function.Surjective p')
    (hip' : Function.Exact i' p')
    (u : K ⟶ K') (v : L ⟶ L') (w : M ⟶ M')
    (hu : i'.comp u.iso.hom.hom.hom = v.iso.hom.hom.hom.comp i)
    (hw : p'.comp v.iso.hom.hom.hom = w.iso.hom.hom.hom.comp p)
    (e : AdmissibleSequence R K.of.obj) (fbar : AdmissibleSequence R M.of.obj) :
    (determinantExactSequenceMap i' p' hi' hp' hip'
      K'.of.property L'.of.property M'.of.property)
        ((determinantFunctor R).mapLinearEquiv u (symbol e) ⊗ₜ[
          IsLocalRing.ResidueField R]
          (determinantFunctor R).mapLinearEquiv w (symbol fbar)) =
      (determinantFunctor R).mapLinearEquiv v
        ((determinantExactSequenceMap i p hi hp hip
          K.of.property L.of.property M.of.property)
          (symbol e ⊗ₜ[IsLocalRing.ResidueField R] symbol fbar)) := by
  let F := determinantFunctor R
  by_cases he : symbol e = 0
  · simp [he]
  by_cases hfbar : symbol fbar = 0
  · simp [hfbar]
  let eu : AdmissibleSequence R K'.of.obj :=
    ⟨(fun a ↦ u.iso.hom.hom.hom (e.1 (Fin.cast (F.map_length u).symm a))),
      F.map_admissible u e⟩
  let fbu : AdmissibleSequence R M'.of.obj :=
    ⟨(fun a ↦ w.iso.hom.hom.hom (fbar.1 (Fin.cast (F.map_length w).symm a))),
      F.map_admissible w fbar⟩
  have heu : symbol eu ≠ 0 := fun h ↦ he <| (F.mapLinearEquiv u).injective <| by
    simpa only [map_zero, F.map_symbol] using h
  have hfbu : symbol fbu ≠ 0 := fun h ↦ hfbar <| (F.mapLinearEquiv w).injective <| by
    simpa only [map_zero, F.map_symbol] using h
  let f : Fin (moduleLength R M.of.obj) → L.of.obj :=
    fun a ↦ Classical.choose (hp (fbar.1 a))
  have hfp : ∀ a, p (f a) = fbar.1 a :=
    fun a ↦ Classical.choose_spec (hp (fbar.1 a))
  obtain ⟨hlen, hadmiss, hsource⟩ :=
    determinantExactSequenceMap_spec i p hi hp hip
      K.of.property L.of.property M.of.property e fbar he hfbar f hfp
  let f' : Fin (moduleLength R M'.of.obj) → L'.of.obj :=
    fun a ↦ v.iso.hom.hom.hom (f (Fin.cast (F.map_length w).symm a))
  have hf'p : ∀ a, p' (f' a) = fbu.1 a := fun a ↦ by
    simpa only [LinearMap.comp_apply, hfp] using
      congrArg (fun g : L.of.obj →ₗ[R] M'.of.obj => g (f (Fin.cast (F.map_length w).symm a))) hw
  obtain ⟨hlen', hadmiss', htarget⟩ :=
    determinantExactSequenceMap_spec i' p' hi' hp' hip'
      K'.of.property L'.of.property M'.of.property eu fbu heu hfbu f' hf'p
  let q : Fin (moduleLength R L.of.obj) → L.of.obj :=
    fun a ↦ Fin.append (fun b ↦ i (e.1 b)) f (Fin.cast hlen a)
  let q' : Fin (moduleLength R L'.of.obj) → L'.of.obj :=
    fun a ↦ Fin.append (fun b ↦ i' (eu.1 b)) f' (Fin.cast hlen' a)
  have hseq : q' = fun a ↦ v.iso.hom.hom.hom
      (q (Fin.cast (F.map_length v).symm a)) := by
    have hsum : ∀ j : Fin (moduleLength R K'.of.obj + moduleLength R M'.of.obj),
        Fin.append (fun b ↦ i' (eu.1 b)) f' j =
          v.iso.hom.hom.hom
            (q (Fin.cast (F.map_length v).symm (Fin.cast hlen'.symm j))) := by
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro b
        let b₀ := Fin.cast (F.map_length u).symm b
        have hidx : Fin.cast hlen
            (Fin.cast (F.map_length v).symm (Fin.cast hlen'.symm (Fin.castAdd
              (moduleLength R M'.of.obj) b))) = Fin.castAdd (moduleLength R M.of.obj) b₀ := by
          apply Fin.ext
          simp [b₀, Fin.val_cast]
        rw [Fin.append_left]
        show i' (eu.1 b) = _
        dsimp only [q]
        rw [hidx, Fin.append_left]
        exact congrArg (fun g : K.of.obj →ₗ[R] L'.of.obj => g (e.1 b₀)) hu
      · intro b
        let b₀ := Fin.cast (F.map_length w).symm b
        have hidx : Fin.cast hlen
            (Fin.cast (F.map_length v).symm (Fin.cast hlen'.symm (Fin.natAdd
              (moduleLength R K'.of.obj) b))) = Fin.natAdd (moduleLength R K.of.obj) b₀ := by
          apply Fin.ext
          simp [b₀, Fin.val_cast, Fin.val_natAdd, ← F.map_length u]
        rw [Fin.append_right]
        show f' b = _
        dsimp only [q]
        rw [hidx, Fin.append_right]
    funext a
    simpa [q', q] using hsum (Fin.cast hlen' a)
  rw [F.map_symbol u e, F.map_symbol w fbar, htarget, hsource,
    F.map_symbol v ⟨q, hadmiss⟩]
  congr 1
  exact Subtype.ext hseq

/-- **Stacks Project, Tag 02PA (`gamma_natural`).** The determinant map of a short
exact sequence is natural under an isomorphism of short exact sequences. -/
@[stacks 02PA "gamma_natural"]
public theorem determinantExactSequenceMap_natural
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K L M K' L' M' : FiniteLengthModuleIso.{u, v} R}
    (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
    (i' : K'.of.obj →ₗ[R] L'.of.obj) (p' : L'.of.obj →ₗ[R] M'.of.obj)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (hi' : Function.Injective i') (hp' : Function.Surjective p')
    (hip' : Function.Exact i' p')
    (u : K ⟶ K') (v : L ⟶ L') (w : M ⟶ M')
    (hu : i'.comp u.iso.hom.hom.hom = v.iso.hom.hom.hom.comp i)
    (hw : p'.comp v.iso.hom.hom.hom = w.iso.hom.hom.hom.comp p) :
    (determinantExactSequenceMap i' p' hi' hp' hip'
      K'.of.property L'.of.property M'.of.property).comp
        (TensorProduct.map
          ((determinantFunctor R).mapLinearEquiv u).toLinearMap
          ((determinantFunctor R).mapLinearEquiv w).toLinearMap) =
      ((determinantFunctor R).mapLinearEquiv v).toLinearMap.comp
        (determinantExactSequenceMap i p hi hp hip
          K.of.property L.of.property M.of.property) := by
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [LinearMap.comp_apply, map_add, hx, hy]
  | tmul x y =>
      refine Submodule.Quotient.induction_on (determinantRelations R K.of.obj) x fun fx ↦ ?_
      refine Submodule.Quotient.induction_on (determinantRelations R M.of.obj) y fun fy ↦ ?_
      induction fx using Finsupp.induction_linear with
      | zero => simp
      | add fx gx hfx hgx =>
          simp only [LinearMap.comp_apply,
            Submodule.Quotient.mk_add, map_add, TensorProduct.add_tmul, hfx, hgx]
      | single e c =>
          induction fy using Finsupp.induction_linear with
          | zero => simp
          | add fy gy hfy hgy =>
              simp only [LinearMap.comp_apply,
                Submodule.Quotient.mk_add, map_add, TensorProduct.tmul_add, hfy, hgy]
          | single f d =>
              have hsym := determinantExactSequenceMap_natural_on_symbols
                i p i' p' hi hp hip hi' hp' hip' u v w hu hw e f
              rw [← Finsupp.smul_single_one e c, ← Finsupp.smul_single_one f d]
              simp only [Submodule.Quotient.mk_smul, LinearMap.comp_apply,
                TensorProduct.map_tmul, map_smul, TensorProduct.smul_tmul,
                TensorProduct.tmul_smul, smul_smul]
              simpa only [symbol, mul_comm, LinearEquiv.coe_toLinearMap] using
                congrArg (fun z ↦ (c * d) • z) hsym

end Module.FiniteLength
end
