module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedVersality.OpennessOfVersalityTransferCounterexampleTarget
public import StacksFrontier.Deformation.Artin.Versality.OpennessTransfer

/-!
# `𝒳′ × 𝒲` has no versal object, so it satisfies openness of versality

Let `𝒴 = 𝒳′ × 𝒲` be the stack `targetBased`, whose objects `(T₀, g)` over a scheme `U` carry a
locally nilpotent function `g`. No object of `𝒴` is versal at any point `u₀ ∈ U`, tested against
the small extensions `l[w]/(w^{m+2}) ⟶ l[w]/(w^{m+1})` with `l = κ(u₀)`. Hence `𝒴` satisfies
openness of versality vacuously.

## Main definitions

* `truncatedRing`: the ring `K[w]/(w^{m+1})`.
* `truncatedObj`: the same ring as an object of the category of Artinian local algebras with
  residue field `K`.

## Main results

* `not_isVersalAt_targetBased`: no object of `𝒴` is versal at any point.
* `hasOpenVersality_targetBased`: `𝒴` satisfies openness of versality.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory Opposite Polynomial Deformation Deformation.Artin

namespace AlgebraicGeometry.PolarizedVersality.OpennessTransfer

/-! ### The truncated polynomial rings `K[w]/(w^{m+1})` -/

section Truncated

variable (K : Type u) [Field K]

/-- The ring `K[w]/(w^{m+1})`. -/
abbrev truncatedRing (m : ℕ) : Type u := AdjoinRoot (X ^ (m + 1) : K[X])

variable {K}

/-- The augmentation `K[w]/(w^{m+1}) ⟶ K`, `w ↦ 0`. -/
def truncatedAug (m : ℕ) : truncatedRing K m →ₐ[K] K :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId K K) 0 (by simp)

/-- The augmentation `K[w]/(w^{m+1}) ⟶ K` is surjective. -/
theorem truncatedAug_surjective (m : ℕ) : Function.Surjective (truncatedAug (K := K) m) :=
  fun c => ⟨algebraMap K _ c, (truncatedAug m).commutes c⟩

/-- The augmentation sends the image of `c ∈ K` to `c`. -/
theorem truncatedAug_algebraMap (m : ℕ) (c : K) :
    truncatedAug m (algebraMap K (truncatedRing K m) c) = c :=
  (truncatedAug m).commutes c

/-- The augmentation sends `w` to `0`. -/
theorem truncatedAug_root (m : ℕ) : truncatedAug (K := K) m (AdjoinRoot.root _) = 0 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- In `K[w]/(w^{m+1})`, `w^{m+1} = 0`. -/
theorem root_pow_succ_truncated (m : ℕ) :
    (AdjoinRoot.root (X ^ (m + 1) : K[X])) ^ (m + 1) = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]

/-- In `K[w]/(w^{m+1})`, `w^m ≠ 0`. -/
theorem root_pow_ne_zero_truncated (m : ℕ) :
    (AdjoinRoot.root (X ^ (m + 1) : K[X])) ^ m ≠ 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow, Ne, AdjoinRoot.mk_eq_zero]
  exact fun h => by simpa using Polynomial.natDegree_le_of_dvd h (pow_ne_zero m X_ne_zero)

/-- An element of the kernel of the augmentation is nilpotent. -/
theorem isNilpotent_of_truncatedAug_eq_zero {m : ℕ} {a : truncatedRing K m}
    (ha : truncatedAug m a = 0) : IsNilpotent a := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  have h0 : p.eval 0 = 0 := by
    change (p.eval₂ (Algebra.ofId K K) 0 : K) = 0 at ha
    simpa [Polynomial.eval₂_eq_eval_map] using ha
  obtain ⟨q, hq⟩ :=
    Polynomial.X_dvd_iff.mpr (by simpa [Polynomial.coeff_zero_eq_eval_zero] using h0)
  refine ⟨m + 1, ?_⟩
  rw [hq, map_mul, mul_pow, AdjoinRoot.mk_X, root_pow_succ_truncated, zero_mul]

/-- An element with nonzero augmentation is a unit. -/
theorem isUnit_of_truncatedAug_ne_zero {m : ℕ} {a : truncatedRing K m}
    (ha : truncatedAug m a ≠ 0) : IsUnit a := by
  have hn : IsNilpotent (a - algebraMap K _ (truncatedAug m a)) :=
    isNilpotent_of_truncatedAug_eq_zero (by rw [map_sub, truncatedAug_algebraMap, sub_self])
  have hu : IsUnit (algebraMap K (truncatedRing K m) (truncatedAug m a)) :=
    (isUnit_iff_ne_zero.mpr ha).map _
  simpa using hn.isUnit_add_left_of_commute hu (Commute.all _ _)

/-- `K[w]/(w^{m+1})` is nontrivial. -/
instance (m : ℕ) : Nontrivial (truncatedRing K m) :=
  (truncatedAug_surjective (K := K) m).nontrivial

/-- `K[w]/(w^{m+1})` is a local ring. -/
instance (m : ℕ) : IsLocalRing (truncatedRing K m) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : truncatedAug m a = 0
  · exact Or.inr (isNilpotent_of_truncatedAug_eq_zero ha).isUnit_one_sub
  · exact Or.inl (isUnit_of_truncatedAug_ne_zero ha)

/-- `K[w]/(w^{m+1})` is finite-dimensional over `K`. -/
instance (m : ℕ) : Module.Finite K (truncatedRing K m) :=
  (AdjoinRoot.powerBasis' (monic_X_pow (m + 1))).finite

/-- `K[w]/(w^{m+1})` is an Artinian ring. -/
instance (m : ℕ) : IsArtinianRing (truncatedRing K m) :=
  IsArtinianRing.of_finite K _

/-- The transition `K[w]/(w^{m+2}) ⟶ K[w]/(w^{m+1})`, `w ↦ w`. -/
def truncatedTransition (m : ℕ) : truncatedRing K (m + 1) →ₐ[K] truncatedRing K m :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId K (truncatedRing K m)) (AdjoinRoot.root _) (by
    rw [eval₂_X_pow, pow_succ, root_pow_succ_truncated, zero_mul])

/-- The transition sends `w` to `w`. -/
theorem truncatedTransition_root (m : ℕ) :
    truncatedTransition (K := K) m (AdjoinRoot.root _) = AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The transition `K[w]/(w^{m+2}) ⟶ K[w]/(w^{m+1})` is surjective. -/
theorem truncatedTransition_surjective (m : ℕ) :
    Function.Surjective (truncatedTransition (K := K) m) := by
  intro a
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  refine ⟨AdjoinRoot.mk _ p, ?_⟩
  show p.eval₂ (algebraMap K (truncatedRing K m)) (AdjoinRoot.root _) = AdjoinRoot.mk _ p
  rw [← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

/-- The transition commutes with the augmentations. -/
theorem truncatedAug_comp_transition (m : ℕ) :
    (truncatedAug (K := K) m).comp (truncatedTransition m) = truncatedAug (m + 1) := by
  apply AdjoinRoot.algHom_ext
  rw [AlgHom.comp_apply, truncatedTransition_root, truncatedAug_root, truncatedAug_root]

/-- The coordinate `w` of `K[w]/(w^{m+1})` as a global function of the spectrum. -/
abbrev truncatedCoord (m : ℕ) : Γ(Spec (.of (truncatedRing K m)), ⊤) :=
  (Scheme.ΓSpecIso (.of (truncatedRing K m))).inv (AdjoinRoot.root (X ^ (m + 1) : K[X]))

/-- The coordinate `w` satisfies `w^{m+1} = 0`. -/
theorem truncatedCoord_pow_succ (m : ℕ) : truncatedCoord (K := K) m ^ (m + 1) = 0 := by
  rw [← map_pow, root_pow_succ_truncated, map_zero]

/-- The coordinate `w` satisfies `w^m ≠ 0`. -/
theorem truncatedCoord_pow_ne_zero (m : ℕ) : truncatedCoord (K := K) m ^ m ≠ 0 := by
  rw [← map_pow]
  intro h
  exact root_pow_ne_zero_truncated m
    ((Scheme.ΓSpecIso (.of (truncatedRing K m))).commRingCatIsoToRingEquiv.symm.injective
      (h.trans (map_zero _).symm))

/-- The basic open of the coordinate `w` is empty. -/
theorem basicOpen_truncatedCoord (m : ℕ) :
    (Spec (.of (truncatedRing K m))).basicOpen (truncatedCoord (K := K) m) = ⊥ :=
  (Scheme.isNilpotent_iff_basicOpen_eq_bot _).mp ⟨m + 1, truncatedCoord_pow_succ m⟩

/-- The augmentation of the image of `a` under the transition is the augmentation of `a`. -/
theorem truncatedAug_transition_apply (m : ℕ) (a : truncatedRing K (m + 1)) :
    truncatedAug m (truncatedTransition m a) = truncatedAug (m + 1) a := by
  rw [← AlgHom.comp_apply, truncatedAug_comp_transition]

variable (Λ : Type u) [CommRing Λ] [Algebra Λ K]

/-- The augmentation of `K[w]/(w^{m+1})`, as a map of `Λ`-algebras for the `Λ`-algebra structure
through `K`. -/
def truncatedAugOver (m : ℕ) :
    letI := ((algebraMap K (truncatedRing K m)).comp (algebraMap Λ K)).toAlgebra
    truncatedRing K m →ₐ[Λ] K :=
  letI := ((algebraMap K (truncatedRing K m)).comp (algebraMap Λ K)).toAlgebra
  { (truncatedAug m).toRingHom with
    commutes' := fun r => truncatedAug_algebraMap m (algebraMap Λ K r) }

/-- **`K[w]/(w^{m+1})` as an Artinian local `Λ`-algebra with residue field `K`**, for the
`Λ`-algebra structure through `K`. -/
def truncatedObj (m : ℕ) : ArtinianLocalAlgCat.{u, u, u} Λ K where
  carrier := truncatedRing K m
  algebra := ((algebraMap K (truncatedRing K m)).comp (algebraMap Λ K)).toAlgebra
  residueEquiv :=
    letI := ((algebraMap K (truncatedRing K m)).comp (algebraMap Λ K)).toAlgebra
    Deformation.residueEquivOfAugmentation (truncatedAugOver Λ m) (truncatedAug_surjective m)

/-- The `Λ`-algebra structure of `truncatedObj Λ m` is the one through `K`. -/
theorem algebraMap_truncatedObj (m : ℕ) (r : Λ) :
    algebraMap Λ (truncatedObj (K := K) Λ m) r =
      algebraMap K (truncatedRing K m) (algebraMap Λ K r) :=
  rfl

/-- The residue map of `truncatedObj Λ m` is the augmentation. -/
theorem residueMap_truncatedObj (m : ℕ) :
    residueMap (truncatedObj (K := K) Λ m) = (truncatedAug (K := K) m).toRingHom :=
  RingHom.ext fun a => by
    let _ := ((algebraMap K (truncatedRing K m)).comp (algebraMap Λ K)).toAlgebra
    exact Deformation.residueEquivOfAugmentation_residue (truncatedAugOver Λ m)
      (truncatedAug_surjective m) a

/-- The transition map as a map of `Λ`-algebras. -/
def truncatedTransitionOver (m : ℕ) :
    truncatedObj (K := K) Λ (m + 1) →ₐ[Λ] truncatedObj (K := K) Λ m where
  toRingHom := (truncatedTransition (K := K) m).toRingHom
  commutes' r := (truncatedTransition m).commutes (algebraMap Λ K r)

/-- The small extension `K[w]/(w^{m+2}) ⟶ K[w]/(w^{m+1})` of Artinian local `Λ`-algebras. -/
def truncatedHom (m : ℕ) : truncatedObj (K := K) Λ (m + 1) ⟶ truncatedObj (K := K) Λ m where
  hom := truncatedTransitionOver Λ m
  isLocal := ⟨fun a ha => by
    refine isUnit_of_truncatedAug_ne_zero fun h0 => ?_
    exact isUnit_iff_ne_zero.mp (ha.map (truncatedAug (K := K) m))
      ((truncatedAug_transition_apply m a).trans h0)⟩
  residue_comm a := by
    let _ := ((algebraMap K (truncatedRing K m)).comp (algebraMap Λ K)).toAlgebra
    let _ := ((algebraMap K (truncatedRing K (m + 1))).comp (algebraMap Λ K)).toAlgebra
    refine (Deformation.residueEquivOfAugmentation_residue (truncatedAugOver Λ m)
      (truncatedAug_surjective m) _).trans ?_
    refine Eq.trans ?_ (Deformation.residueEquivOfAugmentation_residue
      (truncatedAugOver Λ (m + 1)) (truncatedAug_surjective (m + 1)) a).symm
    exact truncatedAug_transition_apply m a

/-- The small extension `K[w]/(w^{m+2}) ⟶ K[w]/(w^{m+1})` is surjective. -/
theorem surjective_truncatedHom (m : ℕ) :
    Function.Surjective (truncatedHom (K := K) Λ m).hom :=
  truncatedTransition_surjective (K := K) m

end Truncated

/-- **A locally nilpotent function has nilpotent germs.** If the basic open of a global function
`g` is empty, its germ at every point is nilpotent. -/
theorem isNilpotent_germ_of_basicOpen_eq_bot {X : Scheme.{u}} {g : Γ(X, ⊤)}
    (hg : X.basicOpen g = ⊥) (p : X) : IsNilpotent (X.presheaf.germ ⊤ p trivial g) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  have hr : X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op g) = ⊥ := by
    rw [Scheme.basicOpen_res, hg, inf_bot_eq]
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : V ≤ ⊤)) p hpV g]
  exact ((Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hV.isCompact _).mpr hr).map _

/-- A morphism `φ : Spec R ⟶ X` from the spectrum of a local ring, sending every point to `p`,
kills `g ^ n` for a global function `g` as soon as the `n`-th power of the germ of `g` at `p`
vanishes. -/
theorem appTop_pow_eq_zero_of_germ {R : CommRingCat.{u}} [IsLocalRing R] {X : Scheme.{u}}
    (φ : Spec R ⟶ X) (g : Γ(X, ⊤)) (n : ℕ) (p : X) (hp : ∀ c, φ c = p)
    (h : X.presheaf.germ ⊤ p trivial g ^ n = 0) :
    φ.appTop (g ^ n) = 0 := by
  have h' : X.presheaf.germ ⊤ (φ (IsLocalRing.closedPoint R)) trivial g ^ n = 0 :=
    (congrArg (fun q : X => X.presheaf.germ ⊤ q trivial g ^ n = 0) (hp _)).mpr h
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk φ, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, Scheme.fromSpecStalk_appTop]
  simp only [CommRingCat.comp_apply, map_pow]
  simp only [← map_pow, h', map_zero]

private theorem comp_id_comp_comp_id {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ 𝟙 Y ≫ g ≫ 𝟙 Z = f ≫ g := by
  simp

private theorem id_comp_comp_id {Y Z : Scheme.{u}} (g : Y ⟶ Z) : 𝟙 Y ≫ g ≫ 𝟙 Z = g := by
  simp

/-! ### The test objects over the truncated polynomial rings -/

section Test

variable {k : Type u} [Field k] {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k)))}
  (x : TargetObj B hS)

/-- The scheme over `Spec k[s,t]` underlying an object of `𝒴`. -/
abbrev targetOver : Over (Spec (.of (MvPolynomial (Fin 2) k))) :=
  ((targetBased B hS).p ⋙ Over.post B.inclusion).obj x

variable (u₀ : (targetOver x).left)

/-- The local ring of `Spec k[s,t]` at the image of `u₀`. -/
abbrev testStalk : Type u :=
  (Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk (basePoint (targetOver x) u₀)

/-- The residue field `l = κ(u₀)`. -/
abbrev testField : Type u := (targetOver x).left.residueField u₀

/-- The Artinian local algebra `l[w]/(w^{m+1})` over the local ring of the base, with the
algebra structure through `l`. -/
def testObj (m : ℕ) : @ArtinianLocalAlgCat.{u, u, u} (testStalk x u₀) (testField x u₀) _ _
    (residueFieldAlgebra (targetOver x) u₀) :=
  @truncatedObj (testField x u₀) _ (testStalk x u₀) _ (residueFieldAlgebra (targetOver x) u₀) m

/-- The small extension `l[w]/(w^{m+2}) ⟶ l[w]/(w^{m+1})`. -/
def testExtension (m : ℕ) : testObj x u₀ (m + 1) ⟶ testObj x u₀ m :=
  @truncatedHom (testField x u₀) _ (testStalk x u₀) _ (residueFieldAlgebra (targetOver x) u₀) m

/-- The structure morphism of `Spec l[w]/(w^{m+1})` over `Spec k[s,t]`, through the local
ring. -/
abbrev testStruct (m : ℕ) :
    Spec (.of (testObj x u₀ m)) ⟶ Spec (.of (MvPolynomial (Fin 2) k)) :=
  letI := residueFieldAlgebra (targetOver x) u₀
  Spec.map (CommRingCat.ofHom (algebraMap (testStalk x u₀) (testObj x u₀ m))) ≫
    (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk (basePoint (targetOver x) u₀)

/-- The structure morphism of `Spec l` over `Spec k[s,t]`, through the local ring. -/
abbrev fieldStruct : Spec (.of (testField x u₀)) ⟶ Spec (.of (MvPolynomial (Fin 2) k)) :=
  letI := residueFieldAlgebra (targetOver x) u₀
  Spec.map (CommRingCat.ofHom (algebraMap (testStalk x u₀) (testField x u₀))) ≫
    (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk (basePoint (targetOver x) u₀)

/-- The site contains `Spec l`. -/
theorem contains_spec_testField : B.Contains (Spec (.of (testField x u₀))) :=
  B.residueField_spec_contains x.base.left.property u₀

/-- The site contains `Spec l[w]/(w^{m+1})`. -/
theorem contains_spec_testObj (m : ℕ) : B.Contains (Spec (.of (testObj x u₀ m))) :=
  Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (testField x u₀) (truncatedRing (testField x u₀) m) (contains_spec_testField x u₀)

/-- `Spec l[w]/(w^{m+1})` as an object of the site. -/
abbrev testSite (m : ℕ) : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS :=
  siteObject B _ hS (contains_spec_testObj x u₀ m) (testStruct x u₀ m)

/-- `Spec l` as an object of the site. -/
abbrev fieldSite : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS :=
  siteObject B _ hS (contains_spec_testField x u₀) (fieldStruct x u₀)

/-- `Spec l[w]/(w^{m+1}) ⟶ Spec l` over `Spec k[s,t]`: the algebra structure is through `l`. -/
def toFieldSite (m : ℕ) : testSite x u₀ m ⟶ fieldSite x u₀ :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
    (algebraMap (testField x u₀) (truncatedRing (testField x u₀) m))))) (by
    apply ObjectProperty.hom_ext
    change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
    rw [← Category.assoc, ← Spec.map_comp]
    rfl)

/-- `Spec l ⟶ U`, the residue field point, over `Spec k[s,t]`. -/
def fieldSiteToBase : fieldSite x u₀ ⟶ x.base :=
  Over.homMk (ObjectProperty.homMk ((targetOver x).left.fromSpecResidueField u₀)) (by
    exact ObjectProperty.hom_ext _ (Scheme.Spec_stalkClosedPointTo_fromSpecStalk
      ((targetOver x).left.fromSpecResidueField u₀ ≫ (targetOver x).hom)).symm)

/-- The coordinate `w` of `l[w]/(w^{m+1})`, as a global function. -/
def testElem (m : ℕ) : functions B hS (testSite x u₀ m) :=
  truncatedCoord (K := testField x u₀) m

/-- The coordinate `w` of `l[w]/(w^{m+1})` satisfies `IsNilpotentPoint`. -/
theorem isNilpotentPoint_testElem (m : ℕ) :
    IsNilpotentPoint B hS (testSite x u₀ m) (testElem x u₀ m) :=
  ⟨basicOpen_truncatedCoord (K := testField x u₀) m,
    ((isArtinAxiomsObject_objFn x).of_hom B hS (fieldSiteToBase x u₀)).of_hom B hS
      (toFieldSite x u₀ m)⟩

/-- **The test object `(Spec l[w]/(w^{m+1}), w)` of `𝒴`.** -/
def testY (m : ℕ) : TargetObj B hS :=
  ⟨testSite x u₀ m, Discrete.mk ⟨testElem x u₀ m, isNilpotentPoint_testElem x u₀ m⟩⟩

/-- The underlying morphism of schemes `Spec l[w]/(w^{m+1}) ⟶ Spec l[w]/(w^{m+2})` of the small
extension, over `Spec k[s,t]`. -/
def testSiteTransition (m : ℕ) : testSite x u₀ m ⟶ testSite x u₀ (m + 1) :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (truncatedTransition (K := testField x u₀) m).toRingHom))) (by
    apply ObjectProperty.hom_ext
    change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun r => (truncatedTransition m).commutes _))

/-- The pullback of `w` along `Spec l[w]/(w^{m+1}) ⟶ Spec l[w]/(w^{m+2})` is `w`. -/
theorem pullbackFunction_testSiteTransition (m : ℕ) :
    testElem x u₀ m =
      pullbackFunction B hS (testSiteTransition x u₀ m) (testElem x u₀ (m + 1)) := by
  have h := congrArg
    (fun φ => φ.hom (AdjoinRoot.root (X ^ (m + 1 + 1) : (testField x u₀)[X])))
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (truncatedTransition (K := testField x u₀) m).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, truncatedTransition_root] at h
  exact h

/-- **The arrow `(Spec l[w]/(w^{m+1}), w) ⟶ (Spec l[w]/(w^{m+2}), w)` of `𝒴`** over the small
extension. -/
def testTransition (m : ℕ) : testY x u₀ m ⟶ testY x u₀ (m + 1) :=
  targetHom B hS (X := testY x u₀ m) (Y := testY x u₀ (m + 1)) (testSiteTransition x u₀ m)
    (Subtype.ext (pullbackFunction_testSiteTransition x u₀ m))

/-- The residue-field condition on an arrow `(Spec l[w]/(w^{m+1}), w) ⟶ x` in the definition of
versality: it restricts to the residue field point `Spec l ⟶ U` of `u₀`. -/
def ResidueCond (m : ℕ) (a : testY x u₀ m ⟶ x) : Prop :=
  Spec.map (CommRingCat.ofHom (truncatedAug (K := testField x u₀) m).toRingHom) ≫
    B.inclusion.map a.base.left = (targetOver x).left.fromSpecResidueField u₀

/-- The residue map of `testObj x u₀ m` is the augmentation. -/
theorem residueMap_testObj (m : ℕ) :
    @residueMap _ _ _ _ (residueFieldAlgebra (targetOver x) u₀) (testObj x u₀ m) =
      (truncatedAug (K := testField x u₀) m).toRingHom :=
  @residueMap_truncatedObj (testField x u₀) _ (testStalk x u₀) _
    (residueFieldAlgebra (targetOver x) u₀) m

/-- The function of `x` vanishes at `u₀`: its pullback to the residue field is zero. -/
theorem pullbackFunction_fieldSiteToBase :
    pullbackFunction B hS (fieldSiteToBase x u₀) (objFn x) = 0 := by
  show ((targetOver x).left.fromSpecResidueField u₀).appTop (objFn x) = 0
  apply eq_zero_of_basicOpen_eq_bot
  refine (Scheme.preimage_basicOpen_top _ _).symm.trans ?_
  have hg : (targetOver x).left.basicOpen (objFn x) = ⊥ := basicOpen_objFn x
  refine (congrArg (fun V => (targetOver x).left.fromSpecResidueField u₀ ⁻¹ᵁ V) hg).trans ?_
  simp

/-- **The arrow `(Spec l, 0) ⟶ x`** over the residue field point. -/
def testBaseHom : testY x u₀ 0 ⟶ x :=
  targetHom B hS (X := testY x u₀ 0) (Y := x) (toFieldSite x u₀ 0 ≫ fieldSiteToBase x u₀)
    (Subtype.ext (by
      change testElem x u₀ 0 = pullbackFunction B hS (toFieldSite x u₀ 0 ≫ fieldSiteToBase x u₀)
        (objFn x)
      rw [pullbackFunction_comp, pullbackFunction_fieldSiteToBase]
      change truncatedCoord (K := testField x u₀) 0 =
        (B.inclusion.map (toFieldSite x u₀ 0).left).appTop 0
      rw [map_zero]
      exact (pow_one _).symm.trans (truncatedCoord_pow_succ (K := testField x u₀) 0)))

/-- The arrow `testBaseHom x u₀` satisfies the residue-field condition. -/
theorem residueCond_testBaseHom : ResidueCond x u₀ 0 (testBaseHom x u₀) := by
  show Spec.map (CommRingCat.ofHom (truncatedAug (K := testField x u₀) 0).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap (testField x u₀) (truncatedRing (testField x u₀) 0))) ≫
      (targetOver x).left.fromSpecResidueField u₀) = _
  rw [← Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap (testField x u₀) (truncatedRing (testField x u₀) 0)) ≫
      CommRingCat.ofHom (truncatedAug (K := testField x u₀) 0).toRingHom = 𝟙 _ :=
    CommRingCat.hom_ext (RingHom.ext fun c => truncatedAug_algebraMap 0 c)
  rw [h, Spec.map_id, Category.id_comp]

/-- If `x` is versal at `u₀`, versality along `l[w]/(w^{m+2}) ⟶ l[w]/(w^{m+1})` extends an arrow
`(Spec l[w]/(w^{m+1}), w) ⟶ x` at `u₀` to an arrow `(Spec l[w]/(w^{m+2}), w) ⟶ x` at `u₀`. -/
theorem exists_testHom_succ
    (hv : IsVersalAt (targetOver x) ((targetBased B hS).p ⋙ Over.post B.inclusion) u₀ x rfl)
    (m : ℕ) (a : testY x u₀ m ⟶ x) (ha : ResidueCond x u₀ m a) :
    ∃ b : testY x u₀ (m + 1) ⟶ x, ResidueCond x u₀ (m + 1) b := by
  obtain ⟨b, hb⟩ := hv (testObj x u₀ m) (testObj x u₀ (m + 1)) (testExtension x u₀ m)
    (@surjective_truncatedHom (testField x u₀) _ (testStalk x u₀) _
      (residueFieldAlgebra (targetOver x) u₀) m)
    (testY x u₀ m) (testY x u₀ (m + 1)) rfl rfl (testTransition x u₀ m)
    (id_comp_comp_id _)
    a (by
      refine (congrArg (· ≫ _) (congrArg Spec.map
        (congrArg CommRingCat.ofHom (residueMap_testObj x u₀ m)))).trans ?_
      exact (comp_id_comp_comp_id _ _).trans ha)
  refine ⟨b, ?_⟩
  have haug : CommRingCat.ofHom (truncatedAug (K := testField x u₀) (m + 1)).toRingHom =
      CommRingCat.ofHom (truncatedTransition (K := testField x u₀) m).toRingHom ≫
        CommRingCat.ofHom (truncatedAug (K := testField x u₀) m).toRingHom :=
    CommRingCat.hom_ext (RingHom.ext fun c => (truncatedAug_transition_apply m c).symm)
  have hcomp :
      Spec.map (CommRingCat.ofHom (truncatedTransition (K := testField x u₀) m).toRingHom) ≫
        B.inclusion.map b.base.left = B.inclusion.map a.base.left := by
    rw [← hb]
    rfl
  unfold ResidueCond at ha ⊢
  rw [haug, Spec.map_comp]
  exact (Category.assoc _ _ _).trans ((congrArg _ hcomp).trans ha)

/-- Versality at `u₀` gives arrows `(Spec l[w]/(w^{m+1}), w) ⟶ x` at `u₀` for every `m`. -/
theorem exists_testHom
    (hv : IsVersalAt (targetOver x) ((targetBased B hS).p ⋙ Over.post B.inclusion) u₀ x rfl) :
    ∀ m : ℕ, ∃ a : testY x u₀ m ⟶ x, ResidueCond x u₀ m a
  | 0 => ⟨testBaseHom x u₀, residueCond_testBaseHom x u₀⟩
  | m + 1 =>
    let ⟨a, ha⟩ := exists_testHom hv m
    exists_testHom_succ x u₀ hv m a ha

/-- **No object of `𝒴` is versal at any point of its base.** -/
theorem not_isVersalAt_targetOver :
    ¬ IsVersalAt (targetOver x) ((targetBased B hS).p ⋙ Over.post B.inclusion) u₀ x rfl := by
  intro hv
  obtain ⟨n, hn⟩ := isNilpotent_germ_of_basicOpen_eq_bot (basicOpen_objFn x) u₀
  obtain ⟨a, ha⟩ := exists_testHom x u₀ hv n
  obtain ⟨φ, hφ⟩ : ∃ φ : Spec (.of (truncatedRing (testField x u₀) n)) ⟶ (targetOver x).left,
      φ = B.inclusion.map a.base.left := ⟨_, rfl⟩
  have ha' : Spec.map (CommRingCat.ofHom (truncatedAug (K := testField x u₀) n).toRingHom) ≫ φ =
      (targetOver x).left.fromSpecResidueField u₀ := hφ ▸ ha
  have hfib : testElem x u₀ n = φ.appTop (objFn x) := hφ ▸ objFn_eq_of_hom B hS a
  have : Subsingleton (Spec (.of (truncatedRing (testField x u₀) n))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (truncatedRing (testField x u₀) n)))
  have h2 : φ (Spec.map (CommRingCat.ofHom (truncatedAug (K := testField x u₀) n).toRingHom)
      (IsLocalRing.closedPoint (testField x u₀))) = u₀ :=
    (congrArg (fun ψ : Spec (.of (testField x u₀)) ⟶ (targetOver x).left =>
      ψ (IsLocalRing.closedPoint (testField x u₀))) ha').trans
      (Scheme.fromSpecResidueField_apply _ _)
  have hpt : ∀ c : Spec (.of (truncatedRing (testField x u₀) n)), φ c = u₀ := fun c => by
    rwa [Subsingleton.elim c (Spec.map (CommRingCat.ofHom
      (truncatedAug (K := testField x u₀) n).toRingHom) (IsLocalRing.closedPoint _))]
  exact truncatedCoord_pow_ne_zero (K := testField x u₀) n ((congrArg (· ^ n) hfib).trans
    ((map_pow _ _ _).symm.trans (appTop_pow_eq_zero_of_germ φ (objFn x) n u₀ hpt hn)))

end Test

/-- **`𝒴 = 𝒳′ × 𝒲` has no versal object**: no object over any scheme `U` over `Spec k[s,t]` is
versal at any point of `U`. -/
theorem not_isVersalAt_targetBased {k : Type u} [Field k] {B : BigFppfSite.{u}}
    {hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k)))}
    (U : Over (Spec (.of (MvPolynomial (Fin 2) k)))) (x : (targetBased B hS).obj)
    (hx : ((targetBased B hS).p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left) :
    ¬ IsVersalAt U ((targetBased B hS).p ⋙ Over.post B.inclusion) u₀ x hx := by
  subst hx
  exact not_isVersalAt_targetOver x u₀

/-- **`𝒴 = 𝒳′ × 𝒲` satisfies openness of versality**, vacuously: it has no versal object. -/
theorem hasOpenVersality_targetBased {k : Type u} [Field k] (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k)))) :
    HasOpenVersality ((targetBased B hS).p ⋙ Over.post B.inclusion) :=
  fun U _ x hx u₀ _ hv => (not_isVersalAt_targetBased U x hx u₀ hv).elim

end AlgebraicGeometry.PolarizedVersality.OpennessTransfer
