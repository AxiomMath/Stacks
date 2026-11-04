module

public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotient

/-!
# Quotients corresponding along an adjunction that is an equivalence on good objects

Let `L ⊣ R` be an adjunction between abelian categories `𝒜` and `ℬ` (`R : 𝒜 ⥤ ℬ`), and let `P`
and `Q` be properties of objects of `𝒜` and `ℬ` such that the counit is invertible on
`P`-objects, the unit on `Q`-objects, `R` carries `P` into `Q`, `L` carries `Q` into `P`, and `Q`
is stable under cokernels and both are stable under isomorphisms.  This is the shape of the
comparison of Stacks 03DX between quasi-coherent modules on the small étale site of a scheme and
on its Zariski site, where neither functor is exact on all modules.

For `A₀` with `P A₀` and an identification `ι : B₀ ≅ R A₀`, the quotients of `A₀` whose target
satisfies `P` correspond to the quotients of `B₀` whose target satisfies `Q`: a quotient
`A₀ ⟶ A₀/K` goes to `B₀ ≅ R A₀ ⟶ R(A₀/K)`.  Quotients are recorded by their kernels, as in
`CategoryTheory.Functor.conjSubobject`.

## Main definitions

* `CategoryTheory.Adjunction.QuotientCorrespondence`: the hypotheses.
* `CategoryTheory.Adjunction.QuotientCorrespondence.rightSubobject`: the subobject of `B₀`
  corresponding to a subobject of `A₀`.
* `CategoryTheory.Adjunction.QuotientCorrespondence.subobjectEquiv`: the bijection.

## Main results

* `CategoryTheory.Adjunction.QuotientCorrespondence.epi_rightProjection`: `R` carries the
  projection onto a `P`-quotient to an epimorphism, although `R` need not preserve epimorphisms.
* `CategoryTheory.Adjunction.QuotientCorrespondence.rightCokernelIso`: the quotient of `B₀` by
  the corresponding subobject is `R` of the quotient of `A₀`.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]
  {L : ℬ ⥤ 𝒜} {R : 𝒜 ⥤ ℬ}

/-- The hypotheses under which an adjunction `L ⊣ R` matches the `P`-quotients of an object of
`𝒜` with the `Q`-quotients of the corresponding object of `ℬ`. -/
structure QuotientCorrespondence (adj : L ⊣ R) (P : ObjectProperty 𝒜) (Q : ObjectProperty ℬ) :
    Prop where
  /-- The counit is invertible on `P`-objects. -/
  isIso_counit : ∀ A, P A → IsIso (adj.counit.app A)
  /-- The unit is invertible on `Q`-objects. -/
  isIso_unit : ∀ B, Q B → IsIso (adj.unit.app B)
  /-- `R` carries `P` into `Q`. -/
  map_right : ∀ A, P A → Q (R.obj A)
  /-- `L` carries `Q` into `P`. -/
  map_left : ∀ B, Q B → P (L.obj B)
  /-- `Q` is stable under cokernels. -/
  cokernel_mem : ∀ {B B' : ℬ} (f : B ⟶ B'), Q B → Q B' → Q (cokernel f)
  /-- `P` is stable under isomorphisms. -/
  of_iso_left : ∀ {A A' : 𝒜}, (A ≅ A') → P A → P A'
  /-- `Q` is stable under isomorphisms. -/
  of_iso_right : ∀ {B B' : ℬ}, (B ≅ B') → Q B → Q B'

namespace QuotientCorrespondence

variable {adj : L ⊣ R} {P : ObjectProperty 𝒜} {Q : ObjectProperty ℬ}
  (h : QuotientCorrespondence adj P Q) {A₀ : 𝒜} (hA₀ : P A₀) {B₀ : ℬ}

/-- The projection of `B₀` onto `R` of the quotient of `A₀` by `K`. -/
abbrev rightProjection (ι : B₀ ≅ R.obj A₀) (K : Subobject A₀) : B₀ ⟶ R.obj (cokernel K.arrow) :=
  ι.hom ≫ R.map (cokernel.π K.arrow)

/-- The subobject of `B₀` corresponding to a subobject `K` of `A₀`: the kernel of
`B₀ ≅ R A₀ ⟶ R(A₀/K)`. -/
abbrev rightSubobject (ι : B₀ ≅ R.obj A₀) (K : Subobject A₀) : Subobject B₀ :=
  kernelSubobject (rightProjection ι K)

/-- `L (R f)` is `f` up to the counit isomorphism at the target. -/
private theorem map_map_eq_counit_comp_comp_inv {C D : Type*} [Category* C] [Category* D]
    {L : D ⥤ C} {R : C ⥤ D} {adj : L ⊣ R} {X Y : C} (f : X ⟶ Y) [IsIso (adj.counit.app Y)] :
    L.map (R.map f) = adj.counit.app X ≫ f ≫ inv (adj.counit.app Y) := by
  rw [← Category.assoc, IsIso.eq_comp_inv]
  exact adj.counit_naturality f

include h hA₀ in
/-- **`R` carries the projection onto a `P`-quotient of `A₀` to an epimorphism.**  The cokernel
`c` of the image is a `Q`-object, so `c ≅ R L c`; and `L c` is the cokernel of `L` of the image,
which is the projection itself up to the counit isomorphisms, hence zero. -/
theorem epi_rightProjection (ι : B₀ ≅ R.obj A₀) (K : Subobject A₀) (hK : P (cokernel K.arrow)) :
    Epi (rightProjection ι K) := by
  have := adj.isLeftAdjoint
  have := adj.isRightAdjoint
  have := h.isIso_counit A₀ hA₀
  have := h.isIso_counit _ hK
  set g := rightProjection ι K
  have hc : Q (cokernel g) := h.cokernel_mem g (h.of_iso_right ι.symm (h.map_right A₀ hA₀))
    (h.map_right _ hK)
  have := h.isIso_unit _ hc
  have hLR := map_map_eq_counit_comp_comp_inv (adj := adj) (cokernel.π K.arrow)
  have hLg : L.map g = L.map ι.hom ≫ adj.counit.app A₀ ≫ cokernel.π K.arrow ≫
      inv (adj.counit.app (cokernel K.arrow)) := by
    simp only [g, rightProjection, Functor.map_comp, hLR]
  have : Epi (L.map g) := by rw [hLg]; infer_instance
  have hz : IsZero (L.obj (cokernel g)) :=
    (isZero_cokernel_of_epi (L.map g)).of_iso (PreservesCokernel.iso L g)
  have hz' : IsZero (cokernel g) :=
    (Functor.map_isZero R hz).of_iso (asIso (adj.unit.app (cokernel g)))
  exact Preadditive.epi_of_isZero_cokernel g hz'

/-- **The quotient of `B₀` by the corresponding subobject is `R` of the quotient of `A₀`.** -/
def rightCokernelIso (ι : B₀ ≅ R.obj A₀) (K : Subobject A₀) (hK : P (cokernel K.arrow)) :
    cokernel (rightSubobject ι K).arrow ≅ R.obj (cokernel K.arrow) :=
  haveI := h.epi_rightProjection hA₀ ι K hK
  Abelian.cokernelKernelSubobjectIso (rightProjection ι K)

include h hA₀ in
/-- The quotient of `B₀` by the corresponding subobject satisfies `Q`. -/
theorem mem_right (ι : B₀ ≅ R.obj A₀) (K : Subobject A₀) (hK : P (cokernel K.arrow)) :
    Q (cokernel (rightSubobject ι K).arrow) :=
  h.of_iso_right (h.rightCokernelIso hA₀ ι K hK).symm (h.map_right _ hK)

/-- The projection of `A₀` onto `L` of the quotient of `B₀` by `K'`, through the counit. -/
abbrev leftProjection (ι : B₀ ≅ R.obj A₀) [IsIso (adj.counit.app A₀)] (K' : Subobject B₀) :
    A₀ ⟶ L.obj (cokernel K'.arrow) :=
  inv (adj.counit.app A₀) ≫ L.map (ι.inv ≫ cokernel.π K'.arrow)

/-- The subobject of `A₀` corresponding to a subobject `K'` of `B₀`. -/
abbrev leftSubobject (ι : B₀ ≅ R.obj A₀) [IsIso (adj.counit.app A₀)] (K' : Subobject B₀) :
    Subobject A₀ :=
  kernelSubobject (leftProjection (adj := adj) ι K')

omit [Abelian 𝒜] in
/-- The projection `leftProjection` is an epimorphism: `L` is a left adjoint, so it preserves
epimorphisms. -/
theorem epi_leftProjection (ι : B₀ ≅ R.obj A₀) [IsIso (adj.counit.app A₀)]
    (K' : Subobject B₀) : Epi (leftProjection (adj := adj) ι K') := by
  have := adj.isLeftAdjoint
  infer_instance

include h in
/-- The quotient of `A₀` by the subobject corresponding to a `Q`-quotient satisfies `P`. -/
theorem mem_left (ι : B₀ ≅ R.obj A₀) [IsIso (adj.counit.app A₀)] (K' : Subobject B₀)
    (hK' : Q (cokernel K'.arrow)) : P (cokernel (leftSubobject (adj := adj) ι K').arrow) :=
  have := epi_leftProjection (adj := adj) ι K'
  h.of_iso_left (Abelian.cokernelKernelSubobjectIso (leftProjection (adj := adj) ι K')).symm
    (h.map_left _ hK')

/-- Equal morphisms have equal kernel subobjects; the existence-of-kernel instances are
propositions, so no transport is needed. -/
theorem kernelSubobject_congr {X Y : 𝒜} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (e : f = g) :
    kernelSubobject f = kernelSubobject g := by
  subst e
  rfl

include h hA₀ in
/-- Going to `B₀` and back recovers a `P`-quotient of `A₀`. -/
theorem left_right (ι : B₀ ≅ R.obj A₀) [IsIso (adj.counit.app A₀)] (K : Subobject A₀)
    (hK : P (cokernel K.arrow)) :
    leftSubobject (adj := adj) ι (rightSubobject ι K) = K := by
  have := h.epi_rightProjection hA₀ ι K hK
  have := h.isIso_counit _ hK
  set e := Abelian.cokernelKernelSubobjectIso (rightProjection ι K)
  have hπ : ι.inv ≫ cokernel.π (rightSubobject ι K).arrow =
      R.map (cokernel.π K.arrow) ≫ e.inv := by
    have h0 := Abelian.cokernelKernelSubobjectIso_inv_comp (rightProjection ι K)
    rw [← h0]
    show ι.inv ≫ (ι.hom ≫ R.map (cokernel.π K.arrow)) ≫ e.inv = _
    rw [Category.assoc, Iso.inv_hom_id_assoc]
  have hLR := map_map_eq_counit_comp_comp_inv (adj := adj) (cokernel.π K.arrow)
  have key : leftProjection (adj := adj) ι (rightSubobject ι K) =
      cokernel.π K.arrow ≫ inv (adj.counit.app (cokernel K.arrow)) ≫ L.map e.inv := by
    simp only [leftProjection, hπ, Functor.map_comp, hLR, Category.assoc,
      IsIso.inv_hom_id_assoc]
  exact (kernelSubobject_congr key).trans
    ((kernelSubobject_comp_mono _ _).trans (kernelSubobject_cokernel_π K))

include h in
/-- Going to `A₀` and back recovers a `Q`-quotient of `B₀`. -/
theorem right_left (ι : B₀ ≅ R.obj A₀) [IsIso (adj.counit.app A₀)] (K' : Subobject B₀)
    (hK' : Q (cokernel K'.arrow)) :
    rightSubobject ι (leftSubobject (adj := adj) ι K') = K' := by
  have := h.isIso_unit _ hK'
  have := epi_leftProjection (adj := adj) ι K'
  set e := Abelian.cokernelKernelSubobjectIso (leftProjection (adj := adj) ι K')
  have hRinv : R.map (inv (adj.counit.app A₀)) = adj.unit.app (R.obj A₀) := by
    rw [Functor.map_inv]
    exact IsIso.inv_eq_of_inv_hom_id (adj.right_triangle_components A₀)
  have h1 : cokernel.π (leftSubobject (adj := adj) ι K').arrow =
      leftProjection (adj := adj) ι K' ≫ e.inv :=
    (Abelian.cokernelKernelSubobjectIso_inv_comp _).symm
  have hn : adj.unit.app (R.obj A₀) ≫ R.map (L.map ι.inv) ≫ R.map (L.map (cokernel.π K'.arrow)) =
      ι.inv ≫ cokernel.π K'.arrow ≫ adj.unit.app (cokernel K'.arrow) := by
    simp
  have key : rightProjection ι (leftSubobject (adj := adj) ι K') =
      cokernel.π K'.arrow ≫ adj.unit.app (cokernel K'.arrow) ≫ R.map e.inv := by
    simp only [rightProjection, h1, leftProjection, Functor.map_comp, hRinv, Category.assoc,
      reassoc_of% hn, Iso.hom_inv_id_assoc]
  exact (kernelSubobject_congr key).trans
    ((kernelSubobject_comp_mono _ _).trans (kernelSubobject_cokernel_π K'))

/-- **The bijection between the `P`-quotients of `A₀` and the `Q`-quotients of `B₀`.** -/
def subobjectEquiv (ι : B₀ ≅ R.obj A₀) [IsIso (adj.counit.app A₀)] :
    {K : Subobject A₀ // P (cokernel K.arrow)} ≃ {K' : Subobject B₀ // Q (cokernel K'.arrow)} where
  toFun K := ⟨rightSubobject ι K.1, h.mem_right hA₀ ι K.1 K.2⟩
  invFun K' := ⟨leftSubobject (adj := adj) ι K'.1, h.mem_left ι K'.1 K'.2⟩
  left_inv K := Subtype.ext (h.left_right hA₀ ι K.1 K.2)
  right_inv K' := Subtype.ext (h.right_left ι K'.1 K'.2)

end QuotientCorrespondence

end CategoryTheory.Adjunction

end
