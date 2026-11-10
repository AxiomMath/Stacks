module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.Topology.Sheaves.Flasque.CokernelGluing

/-!
# The complex of morphisms of inverse images over the opens of a space

Let `P` be a coherent pullback pseudofunctor datum of additive functors on a category `A`, with
fibres preadditive categories `M a`, and let `κ` be a cone over `a₀` from a functor
`π : Opens X₀ ⥤ A` on the opens of a topological space.  For objects `N`, `N'` of `M a₀` the
relative Hom functor `W ↦ Hom((κ W)^*N, (κ W)^*N')` is a presheaf of abelian groups on the opens
of `X₀` (`CategoryTheory.PullbackData.relHomOpens`), and for complexes `K`, `L` of `M a₀` so is
the complex `W ↦ Hom^•((κ W)^*K, (κ W)^*L)` of morphisms of the inverse images, degreewise
(`CategoryTheory.PullbackData.cochainOpens`), with its cocycles
(`CategoryTheory.PullbackData.cocycleOpens`).  The differential commutes with the restriction
maps (`CategoryTheory.PullbackData.cochainRes_δ`).

If every relative Hom presheaf is a sheaf, so are the cochains and the cocycles; if the relative
Hom presheaves into injective objects are flasque and the terms of `L` are injective, the
cochains are flasque.  With exactness in degree `-1` this is the input
`Stacks.FlasqueCokernel.FlasqueTriple` of the gluing of degree `0` cohomology classes
(`CategoryTheory.PullbackData.cochainFlasqueTriple`).

Nothing here is registered.

## Main definitions

* `CategoryTheory.PullbackData.relHomOpens`, `.cochainOpens`, `.cocycleOpens`.
* `CategoryTheory.PullbackData.cochainFlasqueTriple`.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace CochainComplex.HomComplex
open Stacks.FlasqueCokernel

universe v₀ v₁ u₁ v₂ u₂

namespace CategoryTheory.PullbackData

variable {X₀ : Type v₀} [TopologicalSpace X₀]
  {A : Type u₁} [Category.{v₁} A] {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]
  [∀ a, Preadditive (M a)] (P : PullbackData A M)
  [hadd : ∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive] (hP : P.IsCoherent)
  {π : Opens X₀ ⥤ A} {a₀ : A} (κ : ConeTo π a₀)

/-! ### Relative Hom groups -/

section RelHom

variable {I : Type*} [Category* I] {π' : I ⥤ A} (κ' : ConeTo π' a₀)

/-- The transition map of the relative Hom functor is additive. -/
theorem relHomMap_add (N N' : M a₀) {j i : I} (g : j ⟶ i) (α β : P.relHomObj κ' N N' i) :
    P.relHomMap κ' N N' g (α + β) = P.relHomMap κ' N N' g α + P.relHomMap κ' N N' g β := by
  simp [relHomMap, Functor.conjHom, Preadditive.comp_add, Preadditive.add_comp]

/-- The transition map of the relative Hom functor sends `0` to `0`. -/
theorem relHomMap_zero (N N' : M a₀) {j i : I} (g : j ⟶ i) :
    P.relHomMap κ' N N' g 0 = 0 := by
  simp [relHomMap, Functor.conjHom]

/-- The transition map of the relative Hom functor commutes with integer multiples. -/
theorem relHomMap_zsmul (N N' : M a₀) {j i : I} (g : j ⟶ i) (k : ℤ)
    (α : P.relHomObj κ' N N' i) :
    P.relHomMap κ' N N' g (k • α) = k • P.relHomMap κ' N N' g α := by
  simp [relHomMap, Functor.conjHom]

/-- The transition map of the relative Hom functor commutes with multiplication by a unit
of `ℤ`. -/
theorem relHomMap_units_smul (N N' : M a₀) {j i : I} (g : j ⟶ i) (k : ℤˣ)
    (α : P.relHomObj κ' N N' i) :
    P.relHomMap κ' N N' g (k • α) = k • P.relHomMap κ' N N' g α := by
  rw [Units.smul_def, Units.smul_def, relHomMap_zsmul]

omit [∀ a, Preadditive (M a)] hadd in
/-- The transition map of the relative Hom functor commutes with postcomposition by the
inverse image of a morphism `N' ⟶ N''`. -/
theorem relHomMap_comp_pullMap {N N' N'' : M a₀} {j i : I} (g : j ⟶ i)
    (α : P.relHomObj κ' N N' i) (v : N' ⟶ N'') :
    P.relHomMap κ' N N'' g (α ≫ (P.pull (κ'.leg i)).map v) =
      P.relHomMap κ' N N' g α ≫ (P.pull (κ'.leg j)).map v := by
  simp only [relHomMap, Functor.conjHom, Functor.map_comp, Category.assoc]
  congr 2
  exact (P.triangle (κ'.w g)).inv.naturality v

omit [∀ a, Preadditive (M a)] hadd in
/-- The transition map of the relative Hom functor commutes with precomposition by the
inverse image of a morphism `N ⟶ N'`. -/
theorem relHomMap_pullMap_comp {N N' N'' : M a₀} {j i : I} (g : j ⟶ i) (u : N ⟶ N')
    (α : P.relHomObj κ' N' N'' i) :
    P.relHomMap κ' N N'' g ((P.pull (κ'.leg i)).map u ≫ α) =
      (P.pull (κ'.leg j)).map u ≫ P.relHomMap κ' N' N'' g α := by
  have hn := (P.triangle (κ'.w g)).hom.naturality u
  simp only [Functor.comp_map] at hn
  simp only [relHomMap, Functor.conjHom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]

end RelHom

/-- **The relative Hom functor on the opens of `X₀`, as a presheaf of abelian groups.** -/
def relHomOpens (N N' : M a₀) : OpensPresheafData.{v₀, v₂} X₀ where
  obj W := P.relHomObj κ N N' W
  addCommGroup _ := inferInstance
  res {_U _V} h :=
    { toFun := P.relHomMap κ N N' (homOfLE h)
      map_zero' := P.relHomMap_zero κ N N' (homOfLE h)
      map_add' := P.relHomMap_add κ N N' (homOfLE h) }
  res_self {U} _h x := P.relHomMap_id hP κ N N' U x
  res_res {_U _V _W} h h' x := (P.relHomMap_comp hP κ N N' (homOfLE h') (homOfLE h) x).symm

/-- The restriction maps of `relHomOpens` are the transition maps of the relative Hom
functor. -/
theorem relHomOpens_res (N N' : M a₀) {U V : Opens X₀} (h : V ≤ U)
    (x : P.relHomObj κ N N' U) :
    (P.relHomOpens hP κ N N').res h x = P.relHomMap κ N N' (homOfLE h) x :=
  rfl

/-! ### The complex of morphisms -/

variable (K L : CochainComplex (M a₀) ℤ)

/-- The inverse image of a complex along the leg of the cone at an open. -/
abbrev legComplex (K : CochainComplex (M a₀) ℤ) (W : Opens X₀) :
    CochainComplex (M (π.obj W)) ℤ :=
  ((P.pull (κ.leg W)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- **Restriction of cochains**, degreewise the inverse image along the transition morphism read
through the comparison of the legs. -/
def cochainRes (n : ℤ) {U V : Opens X₀} (h : V ≤ U) :
    Cochain (P.legComplex κ K U) (P.legComplex κ L U) n →+
      Cochain (P.legComplex κ K V) (P.legComplex κ L V) n where
  toFun z := Cochain.mk fun p q hpq => P.relHomMap κ (K.X p) (L.X q) (homOfLE h) (z.v p q hpq)
  map_zero' := Cochain.ext _ _ fun p q hpq => by
    simp only [Cochain.mk_v, Cochain.zero_v]
    exact P.relHomMap_zero κ _ _ _
  map_add' z z' := Cochain.ext _ _ fun p q hpq => by
    simp only [Cochain.mk_v, Cochain.add_v]
    exact P.relHomMap_add κ _ _ _ _ _

/-- The components of a restricted cochain are the restrictions of its components. -/
theorem cochainRes_v (n : ℤ) {U V : Opens X₀} (h : V ≤ U)
    (z : Cochain (P.legComplex κ K U) (P.legComplex κ L U) n) (p q : ℤ) (hpq : p + n = q) :
    (P.cochainRes κ K L n h z).v p q hpq =
      P.relHomMap κ (K.X p) (L.X q) (homOfLE h) (z.v p q hpq) :=
  rfl

/-- **The differential commutes with restriction.** -/
theorem cochainRes_δ (n m : ℤ) (hnm : n + 1 = m) {U V : Opens X₀} (h : V ≤ U)
    (z : Cochain (P.legComplex κ K U) (P.legComplex κ L U) n) :
    P.cochainRes κ K L m h (δ n m z) = δ n m (P.cochainRes κ K L n h z) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [cochainRes_v, δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
    δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl, relHomMap_add, relHomMap_units_smul,
    cochainRes_v, cochainRes_v]
  change P.relHomMap κ _ _ _ (z.v p (q - 1) _ ≫ (P.pull (κ.leg U)).map (L.d (q - 1) q)) +
      m.negOnePow • P.relHomMap κ _ _ _ ((P.pull (κ.leg U)).map (K.d p (p + 1)) ≫
        z.v (p + 1) q _) = _
  rw [relHomMap_comp_pullMap, relHomMap_pullMap_comp]
  rfl

/-- **The cochains of degree `n`, as a presheaf on the opens of `X₀`.** -/
def cochainOpens (n : ℤ) : OpensPresheafData.{v₀, v₂} X₀ where
  obj W := Cochain (P.legComplex κ K W) (P.legComplex κ L W) n
  addCommGroup _ := inferInstance
  res h := P.cochainRes κ K L n h
  res_self {U} h z := Cochain.ext _ _ fun p q hpq => by
    rw [cochainRes_v]
    exact P.relHomMap_id hP κ _ _ U _
  res_res {U V W} h h' z := Cochain.ext _ _ fun p q hpq => by
    rw [cochainRes_v, cochainRes_v, cochainRes_v]
    exact (P.relHomMap_comp hP κ _ _ (homOfLE h') (homOfLE h) _).symm

/-- **The cocycles of degree `0`, as a presheaf on the opens of `X₀`.** -/
def cocycleOpens : OpensPresheafData.{v₀, v₂} X₀ where
  obj W := Cocycle (P.legComplex κ K W) (P.legComplex κ L W) 0
  addCommGroup _ := inferInstance
  res {U V} h :=
    { toFun := fun z => Cocycle.mk (P.cochainRes κ K L 0 h z.1) 1 (zero_add 1) (by
        rw [← cochainRes_δ _ _ _ _ 0 1 (zero_add 1), Cocycle.δ_eq_zero, map_zero])
      map_zero' := Cocycle.ext (map_zero _)
      map_add' z z' := Cocycle.ext (map_add (P.cochainRes κ K L 0 h) z.1 z'.1) }
  res_self h z := Cocycle.ext ((P.cochainOpens hP κ K L 0).res_self h z.1)
  res_res h h' z := Cocycle.ext ((P.cochainOpens hP κ K L 0).res_res h h' z.1)

/-- The underlying cochain of a restricted cocycle is the restriction of its underlying
cochain. -/
theorem cocycleOpens_res_coe {U V : Opens X₀} (h : V ≤ U)
    (z : Cocycle (P.legComplex κ K U) (P.legComplex κ L U) 0) :
    (((P.cocycleOpens hP κ K L).res h z :
      Cocycle (P.legComplex κ K V) (P.legComplex κ L V) 0).1) =
      P.cochainRes κ K L 0 h z.1 :=
  rfl

/-! ### Sheaf and flasque properties -/

/-- If the relative Hom presheaves are sheaves, so are the cochains of every degree. -/
theorem cochainOpens_isSheaf (hsh : ∀ N N' : M a₀, (P.relHomOpens hP κ N N').IsSheaf) (n : ℤ) :
    (P.cochainOpens hP κ K L n).IsSheaf := by
  intro U ι V hV hsup s hs
  have key := fun p q (hpq : p + n = q) =>
    hsh (K.X p) (L.X q) U V hV hsup (fun i => (s i).v p q hpq) fun i k =>
      Cochain.congr_v (hs i k) p q hpq
  choose x hx hu using key
  refine ⟨Cochain.mk x, fun i => Cochain.ext _ _ fun p q hpq => ?_, fun y hy =>
    Cochain.ext _ _ fun p q hpq => ?_⟩
  · change (P.cochainRes κ K L n (hV i) (Cochain.mk x)).v p q hpq = _
    exact hx p q hpq i
  · exact hu p q hpq _ fun i => Cochain.congr_v (hy i) p q hpq

/-- If the relative Hom presheaves are sheaves, so are the degree `0` cocycles. -/
theorem cocycleOpens_isSheaf (hsh : ∀ N N' : M a₀, (P.relHomOpens hP κ N N').IsSheaf) :
    (P.cocycleOpens hP κ K L).IsSheaf := by
  intro U ι V hV hsup s hs
  have h0 := P.cochainOpens_isSheaf hP κ K L hsh 0
  have h1 := P.cochainOpens_isSheaf hP κ K L hsh 1
  obtain ⟨x, hx, hxu⟩ := h0 U V hV hsup
    (fun i => (show Cocycle (P.legComplex κ K (V i)) (P.legComplex κ L (V i)) 0 from s i).1)
    fun i k => congrArg Subtype.val (hs i k)
  have hδ : δ 0 1 x = 0 := by
    refine (h1 U V hV hsup (fun i => 0) fun i k => by simp).unique (fun i => ?_) fun i => ?_
    · refine (P.cochainRes_δ κ K L 0 1 (zero_add 1) (hV i) x).trans ?_
      change δ 0 1 ((P.cochainOpens hP κ K L 0).res (hV i) x) = 0
      rw [hx i]
      exact Cocycle.δ_eq_zero _ 1
    · exact map_zero _
  refine ⟨Cocycle.mk x 1 (zero_add 1) hδ, fun i => Cocycle.ext (hx i), fun y hy =>
    Cocycle.ext (hxu (show Cocycle (P.legComplex κ K U) (P.legComplex κ L U) 0 from y).1 fun i =>
      congrArg Subtype.val (hy i))⟩

/-- If the relative Hom presheaves into injective objects are flasque and the terms of `L` are
injective, the cochains of every degree are flasque. -/
theorem cochainOpens_isFlasque
    (hfl : ∀ N N' : M a₀, Injective N' → (P.relHomOpens hP κ N N').IsFlasque)
    (hL : ∀ q, Injective (L.X q)) (n : ℤ) : (P.cochainOpens hP κ K L n).IsFlasque := by
  intro U V h z
  choose w hw using fun p q (hpq : p + n = q) => hfl (K.X p) (L.X q) (hL q) h (z.v p q hpq)
  refine ⟨Cochain.mk fun p q hpq =>
    (w p q hpq : (P.legComplex κ K U).X p ⟶ (P.legComplex κ L U).X q),
    Cochain.ext _ _ fun p q hpq => ?_⟩
  exact hw p q hpq

/-- **The complex `Hom^{-2} ⟶ Hom^{-1} ⟶ Z^0` of morphisms over the opens of `X₀`**, as the
input of the gluing of degree `0` cohomology classes: its sheaf and flasque hypotheses come from
those of the relative Hom presheaves, and exactness in degree `-1` is assumed (`hex`). -/
def cochainFlasqueTriple (hsh : ∀ N N' : M a₀, (P.relHomOpens hP κ N N').IsSheaf)
    (hfl : ∀ N N' : M a₀, Injective N' → (P.relHomOpens hP κ N N').IsFlasque)
    (hL : ∀ q, Injective (L.X q))
    (hex : ∀ (W : Opens X₀) (z : Cochain (P.legComplex κ K W) (P.legComplex κ L W) (-1)),
      δ (-1) 0 z = 0 → ∃ e, δ (-2) (-1) e = z) :
    FlasqueTriple.{v₀, v₂} X₀ where
  C₂ := P.cochainOpens hP κ K L (-2)
  C₁ := P.cochainOpens hP κ K L (-1)
  Z := P.cocycleOpens hP κ K L
  d₂ W := (δ_hom ℤ _ _ (-2) (-1)).toAddMonoidHom
  d₁ W :=
    { toFun := fun c => Cocycle.mk (δ (-1) 0 c) 1 (zero_add 1) (δ_δ _ _ _ c)
      map_zero' := Cocycle.ext (map_zero (δ_hom ℤ _ _ (-1) 0))
      map_add' c c' := Cocycle.ext (map_add (δ_hom ℤ _ _ (-1) 0) c c') }
  d₂_res h x := (P.cochainRes_δ κ K L (-2) (-1) (by norm_num) h x).symm
  d₁_res h x := Cocycle.ext (P.cochainRes_δ κ K L (-1) 0 (by norm_num) h x).symm
  d₁_d₂ W x := Cocycle.ext (δ_δ _ _ _ x)
  exact W y hy := hex W y (congrArg Subtype.val hy)
  isSheaf_C₁ := P.cochainOpens_isSheaf hP κ K L hsh (-1)
  isSheaf_Z := P.cocycleOpens_isSheaf hP κ K L hsh
  isFlasque_C₂ := P.cochainOpens_isFlasque hP κ K L hfl hL (-2)
  isFlasque_C₁ := P.cochainOpens_isFlasque hP κ K L hfl hL (-1)

end CategoryTheory.PullbackData

end
