module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionBaseChangeCoefficient
public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPullback
public import StacksFrontier.CategoryTheory.Sites.RingSheafDescent

/-!
# Changing the base of a square-zero extension along a morphism of thickenings of the base

Let `t₂ : (S, 𝒪_S) ⟶ (S'₂, 𝒪_{S'₂})` and `h' : S'₂ ⟶ S'₁` be morphisms of ringed spaces such
that `t₁ = t₂ ≫ h'` and `t₂` are thickenings, let `f : X ⟶ S`, and let
`0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0` be a square-zero extension of `(f ∘ t₁)⁻¹𝒪_{S'₁}`-algebras whose ideal is
identified with `𝒢` bijectively. Suppose a map `c₂ : f^*t₂^*𝒥₂ ⟶ 𝒢` is given such that the
algebra structure of `𝒪'` carries every section `a` of `𝒥₁ = Ker(t₁^♯)` to the value of `c₂` at
`h'^♯ a`. Then `𝒪'` is an `(f ∘ t₂)⁻¹𝒪_{S'₂}`-algebra, compatibly with the given structure along
`h'`, in such a way that every section `s` of `𝒥₂` goes to the value of `c₂` at `s`.

The construction is a descent. On `S'₁`, the second projection of the fibre product
`𝒪_{S'₁} ×_{t₁_*𝒪_S} h'_*𝒪_{S'₂}` onto `h'_*𝒪_{S'₂}` is locally surjective (`t₁^♯` is), and the
map `(a, s) ↦ β(a) + c₂(s - h'^♯ a)` into `(f ∘ t₁)_*𝒪'` is a ring homomorphism killing the
kernel of that projection — this is where the hypothesis on `c₂` is used. It therefore descends
to `h'_*𝒪_{S'₂} ⟶ (f ∘ t₁)_*𝒪' = h'_*(f ∘ t₂)_*𝒪'`, and since the underlying map of `h'` is a
homeomorphism this is `h'_*` of a map `𝒪_{S'₂} ⟶ (f ∘ t₂)_*𝒪'`, whose adjoint is the new algebra
structure.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.BaseChange.fibreValue`: the ring homomorphism
  `(a, s) ↦ β(a) + c₂(s - h'^♯ a)` on the fibre product.
* `AlgebraicGeometry.RingedSpaceThickening.BaseChange.adjointBase₂`: the descended map
  `𝒪_{S'₂} ⟶ (f ∘ t₂)_*𝒪'`.
* `AlgebraicGeometry.RingedSpaceThickening.BaseChange.extension`: `𝒪'` as an extension of
  `(f ∘ t₂)⁻¹𝒪_{S'₂}`-algebras.

## References

* [Stacks Project, Tag 08UA](https://stacks.math.columbia.edu/tag/08UA)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sites.SqZeroPullback
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq
  presentationScalar)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

namespace BaseChange

variable {X S S₁ S₂ : RingedSpace.{u, u}} {f : X ⟶ S} {t₂ : S ⟶ S₂} {h' : S₂ ⟶ S₁}
  {G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

variable (t₂ h') in
/-- The comorphism `t₁^♯ : 𝒪_{S'₁} ⟶ t₁_*𝒪_S` of `t₁ = t₂ ≫ h'`. -/
abbrev sharp₁ : S₁.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (t₂ ≫ h').hom.base).obj
    S.sheaf :=
  thickeningSharp (t₂ ≫ h')

variable (t₂ h') in
/-- `h'_*` of the comorphism `t₂^♯ : 𝒪_{S'₂} ⟶ t₂_*𝒪_S`. -/
abbrev sharp₂ : (TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).obj S₂.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} (t₂ ≫ h').hom.base).obj S.sheaf :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).map (thickeningSharp t₂)

variable (t₂ h') in
/-- The fibre product `𝒪_{S'₁} ×_{t₁_*𝒪_S} h'_*𝒪_{S'₂}` on `S'₁`. -/
abbrev fibre : Sheaf (Opens.grothendieckTopology S₁.carrier) CommRingCat.{u} :=
  fibreSheaf (sharp₁ t₂ h') (sharp₂ t₂ h')

/-- The first component `a` of a section of the fibre product. -/
abbrev fst (V : (Opens S₁.carrier)ᵒᵖ)
    (z : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) : ↥(S₁.presheaf.obj V) :=
  (fibreVal (sharp₁ t₂ h') (sharp₂ t₂ h') V z).1

/-- The second component `s` of a section of the fibre product. -/
abbrev snd (V : (Opens S₁.carrier)ᵒᵖ)
    (z : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) :
    ↥(S₂.presheaf.obj (op ((Opens.map h'.hom.base).obj V.unop))) :=
  (fibreVal (sharp₁ t₂ h') (sharp₂ t₂ h') V z).2

/-- `h'^♯ : 𝒪_{S'₁}(V) ⟶ 𝒪_{S'₂}(h'⁻¹V)`, with its target spelled as sections of `𝒪_{S'₂}`. -/
abbrev hmap (V : (Opens S₁.carrier)ᵒᵖ) (a : ↥(S₁.presheaf.obj V)) :
    ↥(S₂.presheaf.obj (op ((Opens.map h'.hom.base).obj V.unop))) :=
  (h'.hom.c.app V).hom a

/-- The difference `s - h'^♯ a` of the two components of a section of the fibre product. -/
abbrev diff (V : (Opens S₁.carrier)ᵒᵖ)
    (z : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) :
    ↥(S₂.presheaf.obj (op ((Opens.map h'.hom.base).obj V.unop))) :=
  snd V z - hmap V (fst V z)

/-- The two components of a section of the fibre product have the same image in `𝒪_S`. -/
theorem fst_snd (V : (Opens S₁.carrier)ᵒᵖ)
    (z : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) :
    (t₂.hom.c.app (op ((Opens.map h'.hom.base).obj V.unop))).hom (snd V z) =
      (t₂.hom.c.app (op ((Opens.map h'.hom.base).obj V.unop))).hom
        (hmap V (fst V z)) :=
  (fibreVal_mem (sharp₁ t₂ h') (sharp₂ t₂ h') V z).symm

/-- The difference `s - h'^♯ a` lies in `𝒥₂ = Ker(t₂^♯)`. -/
theorem diff_mem (V : (Opens S₁.carrier)ᵒᵖ)
    (z : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) :
    (t₂.hom.c.app (op ((Opens.map h'.hom.base).obj V.unop))).hom (diff V z) = 0 := by
  rw [diff, map_sub]
  exact sub_eq_zero.2 (fst_snd V z)

variable (c₂ : (modulePullback f).obj ((modulePullback t₂).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) ⟶ G)
  (P : AlgebraSquareZeroExtension (f ≫ (t₂ ≫ h')) G) (hP : P.IdealBijective)

/-- The algebra structure `β : 𝒪_{S'₁}(V) ⟶ 𝒪'((f ∘ t₁)⁻¹V)` of `𝒪'`, on sections. -/
abbrev adj (V : (Opens S₁.carrier)ᵒᵖ) (a : ↥(S₁.presheaf.obj V)) :
    ↥(P.sheaf.obj.obj (op ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).obj V.unop))) :=
  (P.adjointBase.hom.app V).hom a

/-- The value `c₂(s - h'^♯ a)` of the prescribed map at the difference of the components. -/
abbrev diffValue (V : (Opens S₁.carrier)ᵒᵖ)
    (z : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) :
    ↥(G.val.obj (op ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).obj V.unop))) :=
  prescribedIdealSection c₂ (op ((Opens.map h'.hom.base).obj V.unop)) (diff V z) (diff_mem V z)

/-- **The value `β(a) + c₂(s - h'^♯ a)`** of a section `(a, s)` of the fibre product. -/
def value (V : (Opens S₁.carrier)ᵒᵖ)
    (z : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) :
    ↥(P.sheaf.obj.obj (op ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).obj V.unop))) :=
  adj P V (fst V z) +
    P.idealIncl hP (op ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).obj V.unop)) (diffValue c₂ V z)

/-! ### The value is a ring homomorphism -/

section Ring

variable (V : (Opens S₁.carrier)ᵒᵖ)
  (z w : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V))

/-- The difference `s - h'^♯ a` is additive in the section `(a, s)`. -/
theorem diff_add : diff V (z + w) = diff V z + diff V w := by
  change (snd V z + snd V w) - hmap V (fst V z + fst V w) =
    (snd V z - hmap V (fst V z)) + (snd V w - hmap V (fst V w))
  rw [hmap, map_add]
  exact (sub_add_sub_comm _ _ _ _).symm

/-- The difference of a product: `s s' - h'^♯(a a') = s (s' - h'^♯ a') + h'^♯ a' (s - h'^♯ a)`. -/
theorem diff_mul : diff V (z * w) = snd V z * diff V w + hmap V (fst V w) * diff V z := by
  change (snd V z * snd V w) - hmap V (fst V z * fst V w) =
    snd V z * (snd V w - hmap V (fst V w)) + hmap V (fst V w) * (snd V z - hmap V (fst V z))
  rw [hmap, hmap, hmap, map_mul]
  ring

/-- The difference `s - h'^♯ a` vanishes at the unit section. -/
theorem diff_one :
    diff V (1 : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) = 0 := by
  change (1 : ↥(S₂.presheaf.obj (op ((Opens.map h'.hom.base).obj V.unop)))) - hmap V 1 = 0
  rw [hmap, map_one, sub_self]

/-- The difference `s - h'^♯ a` vanishes at the zero section. -/
theorem diff_zero :
    diff V (0 : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) = 0 := by
  change (0 : ↥(S₂.presheaf.obj (op ((Opens.map h'.hom.base).obj V.unop)))) - hmap V 0 = 0
  rw [hmap, map_zero, sub_self]

/-- The value `c₂(s - h'^♯ a)` is additive in the section `(a, s)`. -/
theorem diffValue_add : diffValue c₂ V (z + w) = diffValue c₂ V z + diffValue c₂ V w :=
  (prescribedIdealSection_congr c₂ _ (diff_add V z w) _
      (by rw [map_add, diff_mem, diff_mem, add_zero])).trans
    (prescribedIdealSection_add c₂ _ _ _ (diff_mem V z) (diff_mem V w) _)

/-- The value `c₂(s - h'^♯ a)` vanishes when the difference `s - h'^♯ a` does. -/
private theorem diffValue_eq_zero_of_diff_eq_zero (h : diff V z = 0) : diffValue c₂ V z = 0 :=
  (prescribedIdealSection_congr c₂ _ h _ (map_zero _)).trans (prescribedIdealSection_zero c₂ _ _)

/-- The value `c₂(s - h'^♯ a)` vanishes at the zero section. -/
theorem diffValue_zero :
    diffValue c₂ V (0 : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) = 0 :=
  diffValue_eq_zero_of_diff_eq_zero c₂ V _ (diff_zero V)

/-- The value `c₂(s - h'^♯ a)` vanishes at the unit section. -/
theorem diffValue_one :
    diffValue c₂ V (1 : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) = 0 :=
  diffValue_eq_zero_of_diff_eq_zero c₂ V _ (diff_one V)

/-- The comorphism of `f ∘ t₂` at the second component is the comorphism of `f ∘ t₁` at the first
one. -/
theorem comorphism_snd :
    ((f ≫ t₂).hom.c.app (op ((Opens.map h'.hom.base).obj V.unop))).hom (snd V z) =
      ((f ≫ (t₂ ≫ h')).hom.c.app V).hom (fst V z) := by
  change (f.hom.c.app _).hom ((t₂.hom.c.app _).hom (snd V z)) =
    (f.hom.c.app _).hom ((t₂.hom.c.app _).hom ((h'.hom.c.app V).hom (fst V z)))
  rw [fst_snd V z]
  rfl

/-- The comorphism of `f ∘ t₁` on sections, with its target spelled as sections of `𝒪_X`. -/
abbrev scal (a : ↥(S₁.presheaf.obj V)) :
    ↥((ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf).obj.obj
      (op ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).obj V.unop))) :=
  ((f ≫ (t₂ ≫ h')).hom.c.app V).hom a

/-- The value of `c₂` at the difference of a product `z w` is
`a • c₂(diff w) + a' • c₂(diff z)`, where `a` and `a'` are the first components of `z` and `w`
acting through the comorphism of `f ∘ t₁`. -/
theorem diffValue_mul :
    diffValue c₂ V (z * w) =
      scal (f := f) (t₂ := t₂) (h' := h') V (fst V z) • diffValue c₂ V w +
        scal (f := f) (t₂ := t₂) (h' := h') V (fst V w) • diffValue c₂ V z := by
  have h1 : (t₂.hom.c.app (op ((Opens.map h'.hom.base).obj V.unop))).hom
      (snd V z * diff V w) = 0 := by rw [map_mul, diff_mem, mul_zero]
  have h2 : (t₂.hom.c.app (op ((Opens.map h'.hom.base).obj V.unop))).hom
      (hmap V (fst V w) * diff V z) = 0 := by rw [map_mul, diff_mem, mul_zero]
  refine (prescribedIdealSection_congr c₂ _ (diff_mul V z w) _
      (by rw [map_add, h1, h2, add_zero])).trans ?_
  refine (prescribedIdealSection_add c₂ _ _ _ h1 h2 _).trans ?_
  refine congrArg₂ (· + ·) ?_ ?_
  · refine (prescribedIdealSection_mul c₂ _ _ _ (diff_mem V w) h1).trans ?_
    exact congrArg (fun r : ↥((ringSheaf (J := Opens.grothendieckTopology X.carrier)
      X.sheaf).obj.obj (op ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).obj V.unop))) =>
        r • diffValue c₂ V w)
      (comorphism_snd V z)
  · exact prescribedIdealSection_mul c₂ _ _ _ (diff_mem V z) h2

/-- The reduction of the algebra structure is the comorphism of `f ∘ t₁`. -/
theorem presentationScalar_adj (a : ↥(S₁.presheaf.obj V)) :
    presentationScalar P.reduction (op ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).obj V.unop))
      (adj P V a) = scal (f := f) (t₂ := t₂) (h' := h') V a :=
  congrArg (fun k => (k.hom.app V).hom a) P.adjointBase_comp_reduction

/-- The algebra structure `β` is additive on sections. -/
theorem adj_add (a b : ↥(S₁.presheaf.obj V)) : adj P V (a + b) = adj P V a + adj P V b :=
  map_add (P.adjointBase.hom.app V).hom a b

/-- The algebra structure `β` is multiplicative on sections. -/
theorem adj_mul (a b : ↥(S₁.presheaf.obj V)) : adj P V (a * b) = adj P V a * adj P V b :=
  map_mul (P.adjointBase.hom.app V).hom a b

/-- The value `β(a) + c₂(s - h'^♯ a)` is additive in the section `(a, s)`. -/
theorem value_add : value c₂ P hP V (z + w) = value c₂ P hP V z + value c₂ P hP V w := by
  change adj P V (fst V z + fst V w) + P.idealIncl hP _ (diffValue c₂ V (z + w)) =
    (adj P V (fst V z) + P.idealIncl hP _ (diffValue c₂ V z)) +
      (adj P V (fst V w) + P.idealIncl hP _ (diffValue c₂ V w))
  rw [adj_add, diffValue_add, P.idealIncl_add hP]
  abel

/-- The value `β(a) + c₂(s - h'^♯ a)` is `β(a)` when the difference `s - h'^♯ a` vanishes. -/
private theorem value_eq_adj_of_diff_eq_zero (h : diff V z = 0) :
    value c₂ P hP V z = adj P V (fst V z) := by
  unfold value
  rw [diffValue_eq_zero_of_diff_eq_zero c₂ V z h, P.idealIncl_zero hP, add_zero]

/-- The value `β(a) + c₂(s - h'^♯ a)` of the zero section is zero. -/
theorem value_zero :
    value c₂ P hP V (0 : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) = 0 :=
  (value_eq_adj_of_diff_eq_zero c₂ P hP V _ (diff_zero V)).trans
    (map_zero (P.adjointBase.hom.app V).hom)

/-- The value `β(a) + c₂(s - h'^♯ a)` of the unit section is one. -/
theorem value_one :
    value c₂ P hP V (1 : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) = 1 :=
  (value_eq_adj_of_diff_eq_zero c₂ P hP V _ (diff_one V)).trans
    (map_one (P.adjointBase.hom.app V).hom)

/-- The value `β(a) + c₂(s - h'^♯ a)` is multiplicative in the section `(a, s)`. -/
theorem value_mul : value c₂ P hP V (z * w) = value c₂ P hP V z * value c₂ P hP V w := by
  change adj P V (fst V z * fst V w) + P.idealIncl hP _ (diffValue c₂ V (z * w)) =
    (adj P V (fst V z) + P.idealIncl hP _ (diffValue c₂ V z)) *
      (adj P V (fst V w) + P.idealIncl hP _ (diffValue c₂ V w))
  rw [adj_mul, diffValue_mul, P.idealIncl_add hP, add_mul, mul_add, mul_add,
    P.mul_idealIncl hP, P.idealIncl_mul_idealIncl hP,
    mul_comm (P.idealIncl hP _ (diffValue c₂ V z)) (adj P V (fst V w)), P.mul_idealIncl hP,
    presentationScalar_adj, presentationScalar_adj, add_zero]
  abel

end Ring

/-! ### The value is natural -/

section Natural

variable {V W : (Opens S₁.carrier)ᵒᵖ} (i : V ⟶ W)
  (z : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V))

/-- The first component commutes with restriction. -/
theorem fst_map : fst W (((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).map i).hom z) =
    (S₁.presheaf.map i).hom (fst V z) :=
  rfl

/-- The second component commutes with restriction. -/
theorem snd_map : snd W (((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).map i).hom z) =
    (S₂.presheaf.map ((Opens.map h'.hom.base).op.map i)).hom (snd V z) :=
  rfl

/-- `h'^♯` commutes with restriction. -/
theorem hmap_map (a : ↥(S₁.presheaf.obj V)) :
    hmap W ((S₁.presheaf.map i).hom a) =
      (S₂.presheaf.map ((Opens.map h'.hom.base).op.map i)).hom (hmap V a) :=
  NatTrans.naturality_apply h'.hom.c i a

/-- The difference `s - h'^♯ a` commutes with restriction. -/
theorem diff_map : diff W (((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).map i).hom z) =
    (S₂.presheaf.map ((Opens.map h'.hom.base).op.map i)).hom (diff V z) := by
  change snd W _ - hmap W (fst W _) = _
  rw [snd_map, fst_map, hmap_map, diff, map_sub]

/-- The value `c₂(s - h'^♯ a)` commutes with restriction. -/
theorem diffValue_map :
    diffValue c₂ W (((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).map i).hom z) =
      G.val.map ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).op.map i) (diffValue c₂ V z) :=
  (prescribedIdealSection_congr c₂ _ (diff_map i z) _
      ((diff_map i z) ▸ diff_mem W _)).trans
    (prescribedIdealSection_map c₂ ((Opens.map h'.hom.base).op.map i) _ (diff_mem V z) _)

/-- The algebra structure `β` commutes with restriction. -/
theorem adj_map (a : ↥(S₁.presheaf.obj V)) :
    adj P W ((S₁.presheaf.map i).hom a) =
      (P.sheaf.obj.map ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).op.map i)).hom (adj P V a) :=
  NatTrans.naturality_apply P.adjointBase.hom i a

/-- The value `β(a) + c₂(s - h'^♯ a)` commutes with restriction. -/
theorem value_map :
    value c₂ P hP W (((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).map i).hom z) =
      (P.sheaf.obj.map ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).op.map i)).hom
        (value c₂ P hP V z) := by
  change adj P W (fst W _) + P.idealIncl hP _ (diffValue c₂ W _) = _
  rw [fst_map, adj_map, diffValue_map, P.idealIncl_map hP, value, map_add]
  rfl

end Natural

/-- **The ring homomorphism `(a, s) ↦ β(a) + c₂(s - h'^♯ a)`** from the fibre product to
`(f ∘ t₁)_*𝒪'`. -/
def valueHom : fibre t₂ h' ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ (t₂ ≫ h')).hom.base).obj P.sheaf :=
  ⟨{ app := fun V => CommRingCat.ofHom
        { toFun := value c₂ P hP V
          map_one' := value_one c₂ P hP V
          map_mul' := value_mul c₂ P hP V
          map_zero' := value_zero c₂ P hP V
          map_add' := value_add c₂ P hP V }
     naturality := fun _ _ i => CommRingCat.hom_ext (RingHom.ext fun z => value_map c₂ P hP i z) }⟩

/-- On sections, `valueHom` is `(a, s) ↦ β(a) + c₂(s - h'^♯ a)`. -/
theorem valueHom_app (V : (Opens S₁.carrier)ᵒᵖ)
    (z : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V)) :
    (valueHom c₂ P hP).hom.app V z = value c₂ P hP V z :=
  rfl

/-! ### The value kills the kernel of the second projection -/

section Kernel

/-- The value of `c₂` at `h'^♯ a`, for a section `a` of `𝒥₁`, spelled over the preimage of the
open of `a` under `f ∘ t₁`. -/
abbrev presH (V : (Opens S₁.carrier)ᵒᵖ) (a : S₁.presheaf.obj V)
    (ha : ((t₂ ≫ h').hom.c.app V).hom a = 0) :
    ↥(G.val.obj (op ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).obj V.unop))) :=
  prescribedIdealSection c₂ (op ((Opens.map h'.hom.base).obj V.unop)) (hmap V a) ha

variable (hcomp : ∀ (V : (Opens S₁.carrier)ᵒᵖ) (a : S₁.presheaf.obj V)
    (ha : ((t₂ ≫ h').hom.c.app V).hom a = 0),
    P.ideal.app _ ⟨adj P V a, P.adjointBase_mem_kernelIdeal V a ha⟩ = presH c₂ V a ha)

include hcomp in
/-- **The value kills the kernel of the second projection.** A section `(a, 0)` of the fibre
product has `a` in `𝒥₁`, and its value `β(a) + c₂(-h'^♯ a)` vanishes because `β(a)` is the value
of `c₂` at `h'^♯ a` by hypothesis. -/
theorem value_eq_zero (V : (Opens S₁.carrier)ᵒᵖ)
    (z : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V))
    (hz : (fibreSnd (sharp₁ t₂ h') (sharp₂ t₂ h')).hom.app V z = 0) :
    value c₂ P hP V z = 0 := by
  have hs : snd V z = 0 := hz
  have h0 : (t₂.hom.c.app (op ((Opens.map h'.hom.base).obj V.unop))).hom
      (0 : ↥(S₂.presheaf.obj (op ((Opens.map h'.hom.base).obj V.unop)))) = 0 := map_zero _
  have ha : ((t₂ ≫ h').hom.c.app V).hom (fst V z) = 0 := by
    have h := fst_snd V z
    rw [hs, h0] at h
    exact h.symm
  have hd : diff V z = 0 - hmap V (fst V z) := by rw [diff, hs]
  have hv : diffValue c₂ V z = 0 - presH c₂ V (fst V z) ha :=
    (prescribedIdealSection_congr c₂ _ hd _ ((hd ▸ diff_mem V z))).trans
      ((prescribedIdealSection_sub c₂ _ _ _ h0 ha _).trans
        (congrArg (fun x : ↥(G.val.obj (op ((Opens.map (f ≫ (t₂ ≫ h')).hom.base).obj V.unop))) =>
          x - presH c₂ V (fst V z) ha) (prescribedIdealSection_zero c₂ _ h0)))
  have hb : adj P V (fst V z) = P.idealIncl hP _ (presH c₂ V (fst V z) ha) := by
    have h := P.idealIncl_ideal hP _ ⟨adj P V (fst V z), P.adjointBase_mem_kernelIdeal V _ ha⟩
    rw [hcomp V (fst V z) ha] at h
    exact h.symm
  change adj P V (fst V z) + P.idealIncl hP _ (diffValue c₂ V z) = 0
  rw [hb, hv, ← P.idealIncl_add hP, add_sub_cancel, P.idealIncl_zero hP]

end Kernel

/-! ### Direct image along a homeomorphism -/

section Homeo

variable {Y Z : RingedSpace.{u, u}} (g : Y ⟶ Z) [IsIso g.hom.base]

/-- The direct image along a morphism whose underlying map is a homeomorphism is full: a morphism
between direct images is the direct image of a morphism. -/
def unpushforwardOfIso {T T' : Sheaf (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}}
    (δ : (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj T ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj T') : T ⟶ T' :=
  ⟨(TopCat.Presheaf.presheafEquivOfIso CommRingCat.{u}
    (asIso g.hom.base)).fullyFaithfulFunctor.preimage δ.hom⟩

/-- The direct image of `unpushforwardOfIso g δ` is `δ`. -/
theorem pushforward_map_unpushforwardOfIso
    {T T' : Sheaf (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}}
    (δ : (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj T ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj T') :
    (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (unpushforwardOfIso g δ) = δ :=
  Sheaf.hom_ext ((TopCat.Presheaf.presheafEquivOfIso CommRingCat.{u}
    (asIso g.hom.base)).fullyFaithfulFunctor.map_preimage δ.hom)

/-- The direct image along a morphism whose underlying map is a homeomorphism is faithful. -/
theorem pushforward_map_injective_ofIso
    {T T' : Sheaf (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}} {γ₁ γ₂ : T ⟶ T'}
    (h : (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map γ₁ =
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map γ₂) : γ₁ = γ₂ :=
  Sheaf.hom_ext ((TopCat.Presheaf.presheafEquivOfIso CommRingCat.{u}
    (asIso g.hom.base)).fullyFaithfulFunctor.map_injective (congrArg (fun k => k.hom) h))

end Homeo

/-- The underlying map of `h'` is a homeomorphism when those of `t₂` and `t₂ ≫ h'` are. -/
theorem isIso_base (ht₂ : IsThickening t₂) (ht₁ : IsThickening (t₂ ≫ h')) : IsIso h'.hom.base := by
  have : IsIso t₂.hom.base := ht₂.1
  have : IsIso (t₂.hom.base ≫ h'.hom.base) := ht₁.1
  exact IsIso.of_isIso_comp_left t₂.hom.base h'.hom.base

/-- The second projection of the fibre product is locally surjective, as `t₁^♯` is. -/
private theorem isLocallySurjective_fibreSnd_hom (ht₁ : IsThickening (t₂ ≫ h')) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology S₁.carrier)
      (fibreSnd (sharp₁ t₂ h') (sharp₂ t₂ h')).hom :=
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology S₁.carrier)
      (sharp₁ t₂ h').hom := isLocallySurjective_thickeningSharp (t₂ ≫ h') ht₁
  isLocallySurjective_fibreSnd (sharp₁ t₂ h') (sharp₂ t₂ h')

/-! ### The descended algebra structure -/

section Descent

variable (hcomp : ∀ (V : (Opens S₁.carrier)ᵒᵖ) (a : S₁.presheaf.obj V)
    (ha : ((t₂ ≫ h').hom.c.app V).hom a = 0),
    P.ideal.app _ ⟨adj P V a, P.adjointBase_mem_kernelIdeal V a ha⟩ = presH c₂ V a ha)
  (ht₂ : IsThickening t₂) (ht₁ : IsThickening (t₂ ≫ h'))

/-- **The descent** `h'_*𝒪_{S'₂} ⟶ (f ∘ t₁)_*𝒪'` of the value map along the second projection. -/
def descHom : (TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).obj S₂.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ (t₂ ≫ h')).hom.base).obj P.sheaf :=
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology S₁.carrier)
      (sharp₁ t₂ h').hom := isLocallySurjective_thickeningSharp (t₂ ≫ h') ht₁
  haveI := isLocallySurjective_fibreSnd (sharp₁ t₂ h') (sharp₂ t₂ h')
  Stacks.Sites.RingDescent.desc (fibreSnd (sharp₁ t₂ h') (sharp₂ t₂ h')) (valueHom c₂ P hP)
    (fun V z hz => value_eq_zero c₂ P hP hcomp V z hz)

/-- The second projection followed by `descHom` is `valueHom`. -/
theorem fibreSnd_comp_descHom :
    fibreSnd (sharp₁ t₂ h') (sharp₂ t₂ h') ≫ descHom c₂ P hP hcomp ht₁ = valueHom c₂ P hP :=
  have := isLocallySurjective_fibreSnd_hom (t₂ := t₂) (h' := h') ht₁
  Stacks.Sites.RingDescent.comp_desc _ _ _

/-- **The adjoint `𝒪_{S'₂} ⟶ (f ∘ t₂)_*𝒪'` of the new algebra structure**: the descent, read on
`S'₂` through the homeomorphism underlying `h'`. -/
def adjointBase₂ : S₂.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t₂).hom.base).obj P.sheaf :=
  haveI := isIso_base ht₂ ht₁
  unpushforwardOfIso h' (descHom c₂ P hP hcomp ht₁)

/-- The direct image of `adjointBase₂` along `h'` is `descHom`. -/
theorem pushforward_map_adjointBase₂ :
    (TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).map
        (adjointBase₂ c₂ P hP hcomp ht₂ ht₁) = descHom c₂ P hP hcomp ht₁ :=
  have := isIso_base ht₂ ht₁
  pushforward_map_unpushforwardOfIso h' _

/-- **The new algebra structure** `(f ∘ t₂)⁻¹𝒪_{S'₂} ⟶ 𝒪'`. -/
def base₂ : inverseImageBaseRing (f ≫ t₂) ⟶ P.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ t₂).hom.base).homEquiv
    _ _).symm (adjointBase₂ c₂ P hP hcomp ht₂ ht₁)

/-- The adjoint of `base₂` is `adjointBase₂`. -/
theorem adjointBaseHom_base₂ :
    adjointBaseHom f P.sheaf (t := t₂) (base₂ c₂ P hP hcomp ht₂ ht₁) =
      adjointBase₂ c₂ P hP hcomp ht₂ ht₁ :=
  Equiv.apply_symm_apply _ _

/-- The diagonal `𝒪_{S'₁} ⟶ 𝒪_{S'₁} ×_{t₁_*𝒪_S} h'_*𝒪_{S'₂}`, `a ↦ (a, h'^♯ a)`. -/
def diag : S₁.sheaf ⟶ fibre t₂ h' :=
  fibreLift (sharp₁ t₂ h') (sharp₂ t₂ h') (𝟙 S₁.sheaf) (thickeningSharp h') rfl

/-- The diagonal followed by `valueHom` is the given algebra structure `β`. -/
theorem diag_comp_valueHom : diag (t₂ := t₂) (h' := h') ≫ valueHom c₂ P hP = P.adjointBase := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V =>
    CommRingCat.hom_ext (RingHom.ext fun a => ?_)))
  exact value_eq_adj_of_diff_eq_zero c₂ P hP V ((diag (t₂ := t₂) (h' := h')).hom.app V a)
    (sub_self _)

/-- **The new algebra structure restricts to the given one along `h'`.** -/
theorem baseInverseImageRingMap_comp_base₂ :
    baseInverseImageRingMap (f ≫ t₂) h' ≫ base₂ c₂ P hP hcomp ht₂ ht₁ = P.base := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ (t₂ ≫ h')).hom.base).homEquiv _ _).injective
  refine (adjointBaseHom_baseInverseImageRingMap_comp h' (f ≫ t₂) P.sheaf
    (base₂ c₂ P hP hcomp ht₂ ht₁)).trans ?_
  rw [show adjointHom (f ≫ t₂) P.sheaf (base₂ c₂ P hP hcomp ht₂ ht₁) = _ from
    adjointBaseHom_base₂ c₂ P hP hcomp ht₂ ht₁, pushforward_map_adjointBase₂]
  have h2 : thickeningSharp h' = diag (t₂ := t₂) (h' := h') ≫
      fibreSnd (sharp₁ t₂ h') (sharp₂ t₂ h') :=
    (fibreLift_comp_snd _ _ _ _ _).symm
  refine (congrArg (· ≫ descHom c₂ P hP hcomp ht₁) h2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (diag (t₂ := t₂) (h' := h') ≫ ·)
    (fibreSnd_comp_descHom c₂ P hP hcomp ht₁)).trans ?_
  exact diag_comp_valueHom c₂ P hP

/-- **The new algebra structure lies over `𝒪_X`.** -/
theorem base₂_comp_reduction :
    base₂ c₂ P hP hcomp ht₂ ht₁ ≫ P.reduction = structureRingMap (f ≫ t₂) := by
  have := isIso_base ht₂ ht₁
  have := isLocallySurjective_fibreSnd_hom (t₂ := t₂) (h' := h') ht₁
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ t₂).hom.base).homEquiv _ _).injective
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ t₂).hom.base).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ _) (adjointBaseHom_base₂ c₂ P hP hcomp ht₂ ht₁)).trans ?_
  refine Eq.trans ?_ (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ t₂).hom.base).homEquiv _ _).apply_symm_apply
      (⟨(f ≫ t₂).hom.c⟩ : S₂.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t₂).hom.base).obj X.sheaf)).symm
  refine pushforward_map_injective_ofIso h' ?_
  rw [Functor.map_comp, pushforward_map_adjointBase₂]
  refine Stacks.Sites.RingDescent.hom_ext_of_isLocallySurjective
    (fibreSnd (sharp₁ t₂ h') (sharp₂ t₂ h')) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (fibreSnd_comp_descHom c₂ P hP hcomp ht₁)).trans ?_
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V =>
    CommRingCat.hom_ext (RingHom.ext fun z => ?_)))
  change (P.reduction.hom.app _).hom (adj P V (fst V z) + P.idealIncl hP _ (diffValue c₂ V z)) =
    ((f ≫ t₂).hom.c.app (op ((Opens.map h'.hom.base).obj V.unop))).hom (snd V z)
  rw [map_add, P.reduction_idealIncl hP, add_zero]
  exact (presentationScalar_adj P V (fst V z)).trans (comorphism_snd V z).symm

/-- **`𝒪'` as a square-zero extension of `(f ∘ t₂)⁻¹𝒪_{S'₂}`-algebras**: the same sheaf of rings,
reduction and ideal, with the descended algebra structure. -/
def extension : AlgebraSquareZeroExtension (f ≫ t₂) G where
  sheaf := P.sheaf
  base := base₂ c₂ P hP hcomp ht₂ ht₁
  reduction := P.reduction
  base_comp_reduction := base₂_comp_reduction c₂ P hP hcomp ht₂ ht₁
  reduction_surjective := P.reduction_surjective
  ideal := P.ideal

/-- The ideal of `extension` is identified with `G` bijectively. -/
theorem extension_idealBijective : (extension c₂ P hP hcomp ht₂ ht₁).IdealBijective := hP

/-- The adjoint of the algebra structure of `extension` is `adjointBase₂`. -/
theorem extension_adjointBase :
    (extension c₂ P hP hcomp ht₂ ht₁).adjointBase = adjointBase₂ c₂ P hP hcomp ht₂ ht₁ :=
  adjointBaseHom_base₂ c₂ P hP hcomp ht₂ ht₁

/-- The preimage under `h'` of the image under `h'` of an open of `S'₂` is that open. -/
theorem opens_map_inv (ht₂ : IsThickening t₂) (ht₁ : IsThickening (t₂ ≫ h'))
    (W : (Opens S₂.carrier)ᵒᵖ) :
    haveI := isIso_base ht₂ ht₁
    (op ((Opens.map h'.hom.base).obj ((Opens.map (inv h'.hom.base)).obj W.unop)) :
      (Opens S₂.carrier)ᵒᵖ) = W := by
  have := isIso_base ht₂ ht₁
  change op ((Opens.map (h'.hom.base ≫ inv h'.hom.base)).obj W.unop) = W
  rw [IsIso.hom_inv_id]
  rfl

/-- **The new algebra structure induces `c₂` on `𝒥₂`.** -/
theorem extension_ideal_adjointBase (W : (Opens S₂.carrier)ᵒᵖ) (s : S₂.presheaf.obj W)
    (hs : (t₂.hom.c.app W).hom s = 0) :
    (extension c₂ P hP hcomp ht₂ ht₁).ideal.app _
        ⟨((extension c₂ P hP hcomp ht₂ ht₁).adjointBase.hom.app W).hom s,
          (extension c₂ P hP hcomp ht₂ ht₁).adjointBase_mem_kernelIdeal W s hs⟩ =
      prescribedIdealSection c₂ W s hs := by
  have := isIso_base ht₂ ht₁
  let V : (Opens S₁.carrier)ᵒᵖ := op ((Opens.map (inv h'.hom.base)).obj W.unop)
  have eW : (op ((Opens.map h'.hom.base).obj V.unop) : (Opens S₂.carrier)ᵒᵖ) = W :=
    opens_map_inv ht₂ ht₁ W
  let W' : (Opens S₂.carrier)ᵒᵖ := op ((Opens.map h'.hom.base).obj V.unop)
  let e : W ⟶ W' := eqToHom eW.symm
  let s' : S₂.presheaf.obj W' := (S₂.presheaf.map e).hom s
  have hs' : (t₂.hom.c.app W').hom s' = 0 :=
    (NatTrans.naturality_apply t₂.hom.c e s).trans ((congrArg _ hs).trans (map_zero _))
  let z : ↥((fibrePresheaf (sharp₁ t₂ h') (sharp₂ t₂ h')).obj V) :=
    fibreMk (sharp₁ t₂ h') (sharp₂ t₂ h') V 0 s' ((map_zero _).trans hs'.symm)
  -- the value of the descended map at `s'`
  have hval : ((adjointBase₂ c₂ P hP hcomp ht₂ ht₁).hom.app W').hom s' =
      P.idealIncl hP _ (prescribedIdealSection c₂ W' s' hs') := by
    have k1 := congrArg (fun k => (k.hom.app V).hom s')
      (pushforward_map_adjointBase₂ c₂ P hP hcomp ht₂ ht₁)
    have k2 := congrArg (fun k => (k.hom.app V).hom z) (fibreSnd_comp_descHom c₂ P hP hcomp ht₁)
    refine k1.trans (k2.trans ?_)
    change adj P V 0 + P.idealIncl hP _ (diffValue c₂ V z) = _
    have hd : diff V z = s' := by
      change s' - hmap V 0 = s'
      rw [hmap, map_zero, sub_zero]
    rw [show adj P V 0 = 0 from map_zero _, zero_add]
    exact congrArg (P.idealIncl hP _) (prescribedIdealSection_congr c₂ _ hd _ _)
  have hy : ((extension c₂ P hP hcomp ht₂ ht₁).adjointBase.hom.app W).hom s =
      ((adjointBase₂ c₂ P hP hcomp ht₂ ht₁).hom.app W).hom s :=
    congrArg (fun k => (k.hom.app W).hom s) (extension_adjointBase c₂ P hP hcomp ht₂ ht₁)
  have mem : ∀ (U : (Opens S₂.carrier)ᵒᵖ) (u : S₂.presheaf.obj U) (hu : (t₂.hom.c.app U).hom u = 0),
      ((adjointBase₂ c₂ P hP hcomp ht₂ ht₁).hom.app U).hom u ∈
        kernelIdeal P.reduction.hom (op ((Opens.map (f ≫ t₂).hom.base).obj U.unop)) :=
    fun U u hu =>
      (congrArg (fun k => (k.hom.app U).hom u) (extension_adjointBase c₂ P hP hcomp ht₂ ht₁)) ▸
        (extension c₂ P hP hcomp ht₂ ht₁).adjointBase_mem_kernelIdeal U u hu
  have m' := mem W' s' hs'
  have m := mem W s hs
  have hideal' : P.ideal.app _ ⟨((adjointBase₂ c₂ P hP hcomp ht₂ ht₁).hom.app W').hom s', m'⟩ =
      prescribedIdealSection c₂ W' s' hs' :=
    (congrArg (P.ideal.app _) (Subtype.ext hval)).trans
      (P.ideal_idealIncl hP _ (prescribedIdealSection c₂ W' s' hs'))
  -- transport back along `e`
  let e₁ := (Opens.map (f ≫ t₂).hom.base).op.map e
  have hnat : ((adjointBase₂ c₂ P hP hcomp ht₂ ht₁).hom.app W').hom s' =
      (P.sheaf.obj.map e₁).hom (((adjointBase₂ c₂ P hP hcomp ht₂ ht₁).hom.app W).hom s) :=
    NatTrans.naturality_apply (adjointBase₂ c₂ P hP hcomp ht₂ ht₁).hom e s
  have hmap1 := P.ideal.app_map e₁ ⟨((adjointBase₂ c₂ P hP hcomp ht₂ ht₁).hom.app W).hom s, m⟩
  have hmap2 := prescribedIdealSection_map c₂ e s hs hs'
  have hinj := (map_eqToHom_bijective G (congrArg (fun U : (Opens S₂.carrier)ᵒᵖ =>
    op ((Opens.map (f ≫ t₂).hom.base).obj U.unop)) eW.symm)).1
  change P.ideal.app _ ⟨((extension c₂ P hP hcomp ht₂ ht₁).adjointBase.hom.app W).hom s, _⟩ = _
  rw [show (⟨((extension c₂ P hP hcomp ht₂ ht₁).adjointBase.hom.app W).hom s,
      (extension c₂ P hP hcomp ht₂ ht₁).adjointBase_mem_kernelIdeal W s hs⟩ :
        ↥(kernelIdeal P.reduction.hom (op ((Opens.map (f ≫ t₂).hom.base).obj W.unop)))) =
      ⟨((adjointBase₂ c₂ P hP hcomp ht₂ ht₁).hom.app W).hom s, m⟩ from Subtype.ext hy]
  apply hinj
  have he₁ : e₁ = eqToHom (congrArg (fun U : (Opens S₂.carrier)ᵒᵖ =>
      op ((Opens.map (f ≫ t₂).hom.base).obj U.unop)) eW.symm) := Subsingleton.elim _ _
  rw [← he₁]
  refine hmap1.symm.trans ?_
  refine Eq.trans ?_ hmap2
  refine Eq.trans ?_ hideal'
  exact congrArg (P.ideal.app _) (Subtype.ext hnat.symm)

end Descent

end BaseChange

end AlgebraicGeometry.RingedSpaceThickening

end
