module

public import StacksFrontier.AlgebraicGeometry.FreeIndex.Diagram
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# An affine limit of non-affine stages, with a large index

If, in a descent situation, the limit `X = lim Xᵢ` is affine, is some `Xᵢ` affine? Algebraic
spaces here are presheaves on a big fppf site whose schemes have size below a cutoff `κ`, and
`AlgebraicGeometry.Space.DescentSituation` puts no bound on the index. **Without one the answer
is no**, and this file proves it, over the terminal base, for every big fppf site. The bound
`#I < κ.ord.cof` of `AlgebraicGeometry.Space.MorphismDescentSystem.indexSize` excludes this
example.

Let `F` be a field with `κ ≤ #F`, and index by the finite subsets `T` of `F`. The stage at `T`
is the punctured plane `D(x) ∪ D(y) ⊆ 𝔸²` over the countable subring `ℤ[T] ⊆ F`. Every stage is
quasi-compact, quasi-separated and not affine, every transition morphism is affine, and the limit
is the presheaf represented by the empty scheme, which is affine.

## Main definitions

* `AlgebraicGeometry.Space.Refute07SQ.puncturedFunctor`: the punctured plane over a commutative
  ring, as a functor of the ring.
* `AlgebraicGeometry.Space.Refute07SQ.descentSituation`: the descent situation of the
  counterexample.

## Main results

* `AlgebraicGeometry.Space.Refute07SQ.mk_le_of_compatible`: compatible ring maps from the
  subrings `ℤ[T]` of a field into a nonzero ring embed the field into that ring.
* `AlgebraicGeometry.Space.Refute07SQ.isLimitEmptySiteCone`: the limit of the system in the site
  is the empty scheme.
* `AlgebraicGeometry.Space.Refute07SQ.not_isAffineSpace_system_obj`: no stage is affine.
* `AlgebraicGeometry.Space.Refute07SQ.not_forall_exists_isAffineSpace_system_obj`: over
  `AlgebraicGeometry.Space.DescentSituation`, with no bound on the index, an affine limit need
  not have an affine stage.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal Stacks.Refute09ZM

universe u

namespace AlgebraicGeometry.Space.Refute07SQ

/-! ### The punctured plane as a functor of the base ring -/

/-- The punctured plane `D(x) ∪ D(y) ⊆ Spec A[x, y]` over a commutative ring `A`, contravariant
in `A`. The morphism attached to `A' ⟶ A` restricts the morphism of affine planes it induces. -/
def puncturedFunctor : CommRingCat.{u}ᵒᵖ ⥤ Scheme.{u} where
  obj A := punctured A.unop
  map {A A'} φ := (specPlaneMap φ.unop.hom).resLE (puncturedOpen A'.unop) (puncturedOpen A.unop)
    (le_of_eq (preimage_puncturedOpen φ.unop.hom).symm)
  map_id A := by
    rw [← cancel_mono (puncturedOpen A.unop).ι, Scheme.Hom.resLE_comp_ι, Category.id_comp,
      unop_id, CommRingCat.hom_id, specPlaneMap_id, Category.comp_id]
  map_comp {A₁ A₂ A₃} f g := by
    rw [← cancel_mono (puncturedOpen A₃.unop).ι, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, unop_comp, CommRingCat.hom_comp,
      specPlaneMap_comp]

/-- Every morphism of punctured planes induced by a ring homomorphism is affine. -/
instance isAffineHom_puncturedFunctor_map {A A' : CommRingCat.{u}ᵒᵖ} (φ : A ⟶ A') :
    _root_.AlgebraicGeometry.IsAffineHom (puncturedFunctor.map φ) :=
  isAffineHom_resLE_of_eq (specPlaneMap φ.unop.hom) (preimage_puncturedOpen φ.unop.hom).symm

/-- The structure morphism of the punctured plane over its base ring: the open immersion into
the affine plane followed by the projection of the plane. -/
def toSpec : puncturedFunctor.{u} ⟶ Scheme.Spec where
  app A := (puncturedOpen A.unop).ι ≫ specPlaneBase A.unop
  naturality {A A'} φ := by
    change (specPlaneMap φ.unop.hom).resLE _ _ _ ≫ (puncturedOpen A'.unop).ι ≫
        specPlaneBase A'.unop = ((puncturedOpen A.unop).ι ≫ specPlaneBase A.unop) ≫
        Spec.map φ.unop
    rw [Scheme.Hom.resLE_comp_ι_assoc, specPlaneMap_comp_specPlaneBase, Category.assoc,
      CommRingCat.ofHom_hom]

/-- The punctured plane over a countable ring has size `ℵ₀`, at most. -/
theorem size_punctured_le (A : Type u) [CommRing A] [Countable A] :
    (punctured A).size ≤ ℵ₀ := by
  have hc : Countable (MvPolynomial (Fin 2) A) :=
    Function.Injective.countable (f := AddMonoidAlgebra.coeff)
      fun a b h => by cases a; cases b; simp_all
  refine (Scheme.size_coe_opens_le (affinePlane A) (puncturedOpen A)).trans ?_
  rw [Scheme.size_Spec]
  exact max_le le_rfl (Cardinal.mk_le_aleph0)

/-! ### The subrings generated by finite subsets of a field -/

variable (F : Type u) [Field F]

/-- The subrings of `F`, as commutative rings, with the inclusions between them. -/
def subringFunctor : Subring F ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of R
  map h := CommRingCat.ofHom (Subring.inclusion (leOfHom h))
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The subring `ℤ[T]` of `F` generated by a finite subset `T`, as a functor of `T`. -/
def stageFunctor : Finset F ⥤ CommRingCat.{u} :=
  Monotone.functor (f := fun T : Finset F => Subring.closure (↑T : Set F))
    (fun _ _ h => Subring.closure_mono (Finset.coe_subset.mpr h)) ⋙ subringFunctor F

/-- The subring of a field generated by a finite subset is countable. -/
instance countable_stageFunctor_obj (T : Finset F) : Countable ((stageFunctor F).obj T) := by
  have hset : ((Subring.closure (↑T : Set F) : Subring F) : Set F)
      = Set.range (MvPolynomial.aeval (R := ℤ) (Subtype.val : (↑T : Set F) → F)) := by
    have h := Algebra.adjoin_eq_range ℤ (↑T : Set F)
    rw [Algebra.adjoin_int] at h
    exact congrArg (fun S : Subalgebra ℤ F => (S : Set F)) h
  have hc : Countable (MvPolynomial (↑T : Set F) ℤ) :=
    Function.Injective.countable (f := AddMonoidAlgebra.coeff)
      fun a b h => by cases a; cases b; simp_all
  have : Countable ((Subring.closure (↑T : Set F) : Subring F) : Set F) := by
    rw [hset]; exact (Set.countable_range _).to_subtype
  exact this

/-- The subring of a field generated by a finite subset is a nonzero ring. -/
instance nontrivial_stageFunctor_obj (T : Finset F) : Nontrivial ((stageFunctor F).obj T) :=
  inferInstanceAs (Nontrivial (Subring.closure (↑T : Set F)))

/-- **Compatible ring maps from the subrings `ℤ[T]` of a field embed the field.** A family of
ring homomorphisms from the subrings of `F` generated by its finite subsets into a nonzero ring
`A`, compatible with the inclusions, gives an injection of `F` into `A`, sending `x` to the
image of `x ∈ ℤ[{x}]`. -/
theorem mk_le_of_compatible {A : Type u} [CommRing A] [Nontrivial A]
    (ψ : ∀ T : Finset F, Subring.closure (↑T : Set F) →+* A)
    (hψ : ∀ {T T' : Finset F} (h : T ≤ T') (x : Subring.closure (↑T : Set F)),
      ψ T' (Subring.inclusion (Subring.closure_mono (Finset.coe_subset.mpr h)) x) = ψ T x) :
    #F ≤ #A := by
  classical
  refine Cardinal.mk_le_of_injective
    (f := fun x : F => ψ {x} ⟨x, Subring.subset_closure (by simp)⟩) ?_
  intro x y hxy
  simp only at hxy
  by_contra hne
  have hd : x - y ≠ 0 := sub_ne_zero_of_ne hne
  set T : Finset F := {x, y, (x - y)⁻¹} with hT
  have hxT : x ∈ Subring.closure (↑T : Set F) := Subring.subset_closure (by simp [hT])
  have hyT : y ∈ Subring.closure (↑T : Set F) := Subring.subset_closure (by simp [hT])
  have hiT : (x - y)⁻¹ ∈ Subring.closure (↑T : Set F) := Subring.subset_closure (by simp [hT])
  have hsingle : ∀ (z : F) (hz : z ∈ T),
      ψ T ⟨z, Subring.subset_closure hz⟩ = ψ {z} ⟨z, Subring.subset_closure (by simp)⟩ :=
    fun z hz => hψ (show ({z} : Finset F) ≤ T by simpa using hz)
      ⟨z, Subring.subset_closure (by simp)⟩
  have key : (⟨x, hxT⟩ - ⟨y, hyT⟩ : Subring.closure (↑T : Set F)) * ⟨(x - y)⁻¹, hiT⟩ = 1 := by
    apply Subtype.ext
    push_cast
    field_simp
  have hcon := congrArg (ψ T) key
  rw [map_one, map_mul, map_sub, hsingle x (by simp [hT]), hsingle y (by simp [hT]), hxy] at hcon
  simp at hcon

/-- **A cone over the system has an empty vertex.** If a diagram of schemes maps to the
spectra of the rings `ℤ[T]`, and `κ ≤ #F`, then the vertex of any cone over it of size below `κ`
is empty. -/
theorem isEmpty_of_cone {κ : Cardinal.{u}} (hF : κ ≤ #F)
    {G : (Finset F)ᵒᵖ ⥤ Scheme.{u}} (α : G ⟶ (stageFunctor F).op ⋙ Scheme.Spec)
    (s : Cone G) (hs : s.pt.size < κ) : IsEmpty s.pt := by
  by_contra hne
  obtain ⟨z⟩ := not_isEmpty_iff.mp hne
  let l : ∀ T : Finset F, s.pt ⟶ Spec ((stageFunctor F).obj T) :=
    fun T => s.π.app (op T) ≫ α.app (op T)
  have hl : ∀ {T T' : Finset F} (h : T ≤ T'),
      l T' ≫ Spec.map ((stageFunctor F).map (homOfLE h)) = l T := by
    intro T T' h
    have hα := α.naturality (homOfLE h).op
    change G.map (homOfLE h).op ≫ α.app (op T) =
      α.app (op T') ≫ Spec.map ((stageFunctor F).map (homOfLE h)) at hα
    simp only [l, Category.assoc, ← hα]
    rw [← Category.assoc, s.w]
  let ψ : ∀ T : Finset F, (stageFunctor F).obj T →+* s.pt.presheaf.stalk z :=
    fun T => (s.pt.presheaf.germ ⊤ z trivial).hom.comp
      ((Scheme.ΓSpecIso ((stageFunctor F).obj T)).inv ≫ (l T).appTop).hom
  have hψ : ∀ {T T' : Finset F} (h : T ≤ T'),
      (ψ T').comp ((stageFunctor F).map (homOfLE h)).hom = ψ T := by
    intro T T' h
    have key : (Scheme.ΓSpecIso ((stageFunctor F).obj T)).inv ≫ (l T).appTop =
        (stageFunctor F).map (homOfLE h) ≫
          (Scheme.ΓSpecIso ((stageFunctor F).obj T')).inv ≫ (l T').appTop := by
      rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
        ← Scheme.Hom.comp_appTop, hl h]
    simp only [ψ]
    rw [key]
    simp only [CommRingCat.hom_comp, RingHom.comp_assoc]
  have hle := mk_le_of_compatible F ψ fun h x => RingHom.congr_fun (hψ h) x
  exact absurd ((hle.trans (Scheme.mk_stalk_le_size s.pt z)).trans_lt hs) (not_lt.mpr hF)

/-! ### The system in the big fppf site of the terminal scheme -/

variable (B : BigFppfSite.{u})

/-- The punctured plane over `ℤ[T]` belongs to the site. -/
theorem contains_stage (T : Finset F) :
    B.Contains (puncturedFunctor.obj (op ((stageFunctor F).obj T))) :=
  (size_punctured_le _).trans_lt B.aleph0_lt_cutoff

/-- Alias of `AlgebraicGeometry.BigFppfSite.contains_empty`. -/
alias contains_empty := AlgebraicGeometry.BigFppfSite.contains_empty

/-- The stage at `T`, as an object of the big fppf site of the terminal scheme. -/
def siteObj (T : Finset F) : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal :=
  BigFppfOver.mk B _ _ (contains_stage F B T) (terminal.from _)

/-- The system of punctured planes, in the big fppf site of the terminal scheme. -/
def siteDiagram : (Finset F)ᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal where
  obj T := siteObj F B T.unop
  map {_T T'} f := BigFppfOver.homMk B _ _ (contains_stage F B T'.unop) (terminal.from _)
    (((stageFunctor F).op ⋙ puncturedFunctor).map f) (terminal.hom_ext _ _)
  map_id T := BigFppfOver.map_toScheme_injective B _ _
    (((stageFunctor F).op ⋙ puncturedFunctor).map_id T)
  map_comp f g := BigFppfOver.map_toScheme_injective B _ _
    (((stageFunctor F).op ⋙ puncturedFunctor).map_comp f g)

/-- The empty scheme, as an object of the big fppf site of the terminal scheme. -/
def emptyObj : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal :=
  BigFppfOver.mk B _ _ (contains_empty B) (terminal.from _)

/-- Two morphisms out of an object of the site with empty underlying scheme agree. -/
theorem hom_ext_of_isEmpty {T T' : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal}
    (h : IsEmpty ((BigFppfOver.toScheme B _ _).obj T)) (a b : T ⟶ T') : a = b :=
  BigFppfOver.map_toScheme_injective B _ _ ((isInitialOfIsEmpty (X := _)).hom_ext _ _)

/-- The cone over the system with the empty scheme as vertex. -/
def emptySiteCone : Cone (siteDiagram F B) where
  pt := emptyObj B
  π :=
    { app := fun T => BigFppfOver.homMk B _ _ (contains_stage F B T.unop) (terminal.from _)
        (emptyIsInitial.to _) (terminal.hom_ext _ _)
      naturality := fun _ _ _ => hom_ext_of_isEmpty B
        (inferInstanceAs (IsEmpty (∅ : Scheme.{u}))) _ _ }

/-- The vertex of a cone over the system in the site is empty, as soon as `κ ≤ #F`. -/
theorem isEmpty_toScheme_cone_pt (hF : B.cutoff ≤ #F) (s : Cone (siteDiagram F B)) :
    IsEmpty ((BigFppfOver.toScheme B _ _).obj s.pt) :=
  isEmpty_of_cone F hF (G := siteDiagram F B ⋙ BigFppfOver.toScheme B _ _)
    (Functor.whiskerLeft (stageFunctor F).op toSpec)
    ((BigFppfOver.toScheme B _ _).mapCone s) s.pt.left.2

/-- **The limit of the system in the site is the empty scheme**, as soon as `κ ≤ #F`. -/
def isLimitEmptySiteCone (hF : B.cutoff ≤ #F) : IsLimit (emptySiteCone F B) where
  lift s := BigFppfOver.homMk B _ _ (contains_empty B) (terminal.from _)
    (@IsInitial.to _ _ _ (@isInitialOfIsEmpty _ (isEmpty_toScheme_cone_pt F B hF s)) _)
    (terminal.hom_ext _ _)
  fac s _ := hom_ext_of_isEmpty B (isEmpty_toScheme_cone_pt F B hF s) _ _
  uniq s _ _ := hom_ext_of_isEmpty B (isEmpty_toScheme_cone_pt F B hF s) _ _

/-- **The descent situation of the counterexample.** The stages are the functors of points of
the punctured planes over the rings `ℤ[T]`, and the chosen limit is the functor of points of the
empty scheme. -/
def descentSituation [DecidableEq F] (hF : B.cutoff ≤ #F) :
    DescentSituation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal (Finset F) where
  system := siteDiagram F B ⋙ yoneda
  algebraicSpace _ := isAlgebraicSpace_yoneda B _ _ _
  transition_affine _f := isAffineHom_of_presheaf
    ((presheaf_yoneda_map_iff B _ _ (P := @AlgebraicGeometry.IsAffineHom) inferInstance _).2
      (isAffineHom_puncturedFunctor_map _))
  quasiCompact T := isQuasiCompact_yoneda_of_compact B _ _ _
    (inferInstanceAs (CompactSpace (punctured ((stageFunctor F).obj T))))
  quasiSeparated T := isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B _ _ _ _
    ⟨siteObj F B T, inferInstanceAs (QuasiSeparatedSpace (punctured ((stageFunctor F).obj T))),
      ⟨Functor.RepresentableBy.yoneda _⟩⟩
  limitCone := yoneda.mapCone (emptySiteCone F B)
  isLimit := isLimitOfPreserves yoneda (isLimitEmptySiteCone F B hF)
  limitAlgebraicSpace := isAlgebraicSpace_yoneda B _ _ _
  base := ∅

/-- The limit of the counterexample is an affine algebraic space. -/
theorem isAffineSpace_limitCone_pt [DecidableEq F] (hF : B.cutoff ≤ #F) :
    IsAffineSpace B _ _ (descentSituation F B hF).limitCone.pt :=
  isAffineSpace_yoneda B _ _ (emptyObj B) (inferInstanceAs (IsAffine (∅ : Scheme.{u})))

/-- **No stage of the counterexample is affine.** -/
theorem not_isAffineSpace_system_obj [DecidableEq F] (hF : B.cutoff ≤ #F) (T : Finset F) :
    ¬ IsAffineSpace B _ _ ((descentSituation F B hF).system.obj (op T)) := by
  rintro ⟨T', hT', ⟨e⟩⟩
  let e' : siteObj F B T ≅ T' := Yoneda.fullyFaithful.preimageIso e
  have : IsAffine ((BigFppfOver.toScheme B _ _).obj (siteObj F B T)) :=
    IsAffine.of_isIso ((BigFppfOver.toScheme B _ _).mapIso e').hom
  exact not_isAffine_punctured ((stageFunctor F).obj T) this

/-- A field in `Type u` of cardinality at least the cutoff of a big fppf site: rational
functions over `ℚ` in a set of variables of that cardinality. -/
abbrev bigField : Type u := FractionRing (MvPolynomial B.cutoff.out ℚ)

/-- The field `bigField B` has cardinality at least the cutoff. -/
theorem cutoff_le_mk_bigField : B.cutoff ≤ #(bigField B) := by
  have hinj : Function.Injective (fun i : B.cutoff.out =>
      algebraMap (MvPolynomial B.cutoff.out ℚ) (bigField B) (MvPolynomial.X i)) :=
    (IsFractionRing.injective (MvPolynomial B.cutoff.out ℚ) (bigField B)).comp
      MvPolynomial.X_injective
  simpa [Cardinal.mk_out] using Cardinal.mk_le_of_injective hinj

/-- **An affine limit need not have an affine stage.** For every big fppf site, over the terminal
base, it is false that every `AlgebraicGeometry.Space.DescentSituation` (with no bound on the
index) whose limit is affine has an affine stage at or above its base. -/
theorem not_forall_exists_isAffineSpace_system_obj :
    ¬ ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal I),
      IsAffineSpace B (⊤_ Scheme.{u}) B.contains_terminal D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧
        IsAffineSpace B (⊤_ Scheme.{u}) B.contains_terminal (D.system.obj (Opposite.op i)) := by
  classical
  intro h
  obtain ⟨T, -, hT⟩ := h (descentSituation (bigField B) B (cutoff_le_mk_bigField B))
    (isAffineSpace_limitCone_pt (bigField B) B (cutoff_le_mk_bigField B))
  exact not_isAffineSpace_system_obj (bigField B) B (cutoff_le_mk_bigField B) T hT

end AlgebraicGeometry.Space.Refute07SQ

end
