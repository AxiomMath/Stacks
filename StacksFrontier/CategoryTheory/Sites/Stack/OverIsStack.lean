module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack

/-!
# The localization `𝒞/U` is a stack exactly when `h_U` is a sheaf (Stacks 04WU)

Let `(𝒞, J)` be a site and let `U` be an object of `𝒞`. The localization `j_U : 𝒞/U ⥤ 𝒞` is the
forgetful functor `CategoryTheory.Over.forget U`, and it makes `𝒞/U` a category over `𝒞` whose
fibre over `V` is the set `h_U(V) = Hom(V, U)` of sections of the representable presheaf `h_U`,
regarded as a category with exactly one morphism between two equal sections and none otherwise.
This file proves that `j_U` is a stack over `𝒞`, in the sense of
`CategoryTheory.Functor.IsStack` (Stacks 026F), if and only if `h_U` is a sheaf.

## Main results

* `CategoryTheory.Over.isFibered_forget`: `𝒞/U ⥤ 𝒞` is a fibred category, with the pullback of
  `A : 𝒞/U` along `f` given by `f ≫ A.hom`; this is condition (1) of Stacks 026F, and it holds for
  every `U` and every topology.
* `CategoryTheory.Over.isMorSheaf_forget` and
  `CategoryTheory.Over.isSeparatedFor_of_isMorSheaf`: condition (2) of Stacks 026F for `𝒞/U ⥤ 𝒞`
  is separatedness of `h_U`.
* `CategoryTheory.Over.hasEffectiveDescent_forget`: condition (3) of Stacks 026F for `𝒞/U ⥤ 𝒞`
  follows from the sheaf condition on `h_U`.
* `CategoryTheory.Over.isStack_forget_iff_isSheaf`: `j_U` is a stack over `(𝒞, J)` if and only if
  `h_U` is a `J`-sheaf.

## Implementation notes

Conditions (2) and (3) of Stacks 026F are read off `h_U` directly, rather than through the
correspondence between categories fibred in setoids and presheaves. A morphism of `𝒞/U` is
determined by the morphism of `𝒞` it lies over (`CategoryTheory.Over.hom_ext_of_isHomLift`), and
one exists exactly when the two structure morphisms are compatible
(`CategoryTheory.Over.homOfFiberSec`); in particular every fibre is thin.

`CategoryTheory.Over.fiberSec` is the dictionary between the two pictures: it sends an object of
the fibre of `𝒞/U ⥤ 𝒞` over `V` to its structure morphism `V ⟶ U`, i.e. to a section of `h_U` over
`V`, and `CategoryTheory.Over.fiberOfSec` is the inverse construction.

The sieve on `𝒞/V` appearing in condition (2) is transported to a sieve on `V` by
`CategoryTheory.Sieve.overEquiv`, along which `CategoryTheory.GrothendieckTopology.over` is
defined.
-/

@[expose] public section

-- The chosen pullbacks of `CategoryTheory.Functor.IsPreFibered` and the inclusion of a fibre are
-- semireducible, so the endpoints of the composites below agree only up to unfolding them.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Opposite

universe v₁ u₁

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {U : 𝒞}

namespace Over

/-- A morphism `φ` of `𝒞/U` lies over `f : V ⟶ W` through the forgetful functor exactly when its
underlying morphism of `𝒞` is `f`, transported along the identifications of the sources and
targets. -/
lemma isHomLift_forget_iff {A B : Over U} (φ : A ⟶ B) {V W : 𝒞} (f : V ⟶ W)
    (hA : A.left = V) (hB : B.left = W) :
    (Over.forget U).IsHomLift f φ ↔ φ.left = eqToHom hA ≫ f ≫ eqToHom hB.symm := by
  refine ⟨fun h ↦ ?_, fun h ↦ IsHomLift.of_fac' _ f φ hA hB h⟩
  have := h
  exact IsHomLift.fac' (Over.forget U) f φ

/-- A morphism of `𝒞/U` lying over `f` has underlying morphism `f`, up to the identifications of
its source and target. -/
private lemma left_eq_of_isHomLift {A B : Over U} {V W : 𝒞} (f : V ⟶ W) (φ : A ⟶ B)
    (h : (Over.forget U).IsHomLift f φ) :
    φ.left = eqToHom (IsHomLift.domain_eq (Over.forget U) f φ) ≫ f ≫
      eqToHom (IsHomLift.codomain_eq (Over.forget U) f φ).symm := by
  have := h
  exact IsHomLift.fac' (Over.forget U) f φ

/-- Every morphism of `𝒞/U` is strongly cartesian over the morphism of `𝒞` it lies over. -/
lemma isStronglyCartesian_forget {A B : Over U} {V W : 𝒞} (f : V ⟶ W) (φ : A ⟶ B)
    [(Over.forget U).IsHomLift f φ] : (Over.forget U).IsStronglyCartesian f φ where
  universal_property' := by
    intro C g φ' hlift
    have := hlift
    have hA : A.left = V := IsHomLift.domain_eq (Over.forget U) f φ
    have hB : B.left = W := IsHomLift.codomain_eq (Over.forget U) f φ
    have hφ : φ.left = eqToHom hA ≫ f ≫ eqToHom hB.symm := left_eq_of_isHomLift f φ inferInstance
    have hφ' : φ'.left = (g ≫ f) ≫ eqToHom hB.symm :=
      (left_eq_of_isHomLift (g ≫ f) φ' hlift).trans (by simp)
    have hAw : A.hom = φ.left ≫ B.hom := (Over.w φ).symm
    have hCw : C.hom = φ'.left ≫ B.hom := (Over.w φ').symm
    have hleft : (g ≫ eqToHom hA.symm) ≫ A.hom = C.hom := by
      rw [hAw, hCw, hφ, hφ']; simp
    refine ⟨Over.homMk (g ≫ eqToHom hA.symm) hleft, ⟨?_, ?_⟩, ?_⟩
    · exact (isHomLift_forget_iff _ g rfl hA).2 (by simp)
    · exact (Over.forget U).map_injective (by simp [hφ, hφ'])
    · rintro χ ⟨hχ, -⟩
      exact (Over.forget U).map_injective
        (((isHomLift_forget_iff χ g rfl hA).1 hχ).trans (by simp))

/-- `𝒞/U` is a fibred category over `𝒞`: the pullback of `A : 𝒞/U` along `f : V ⟶ A.left` is
`f ≫ A.hom`, and every morphism of `𝒞/U` is strongly cartesian. -/
instance isFibered_forget : (Over.forget U).IsFibered :=
  .of_exists_isStronglyCartesian fun A V f ↦ by
    have : (Over.forget U).IsHomLift f (Over.homMk f rfl : Over.mk (f ≫ A.hom) ⟶ A) :=
      (isHomLift_forget_iff _ f rfl rfl).2 (by simp)
    exact ⟨Over.mk (f ≫ A.hom), Over.homMk f rfl, isStronglyCartesian_forget _ _⟩

/-! ### The fibres of `𝒞/U ⥤ 𝒞` and the presheaf `h_U` -/

/-- The structure morphism of an object of the fibre of `𝒞/U ⥤ 𝒞` over `V`, read as an element
`V ⟶ U` of the representable presheaf `h_U`. -/
def fiberSec {V : 𝒞} (x : (Over.forget U).Fiber V) : V ⟶ U := eqToHom x.2.symm ≫ x.1.hom

/-- A morphism of `𝒞/U` between objects of the fibres over `V` and `W` lying over `f : V ⟶ W`
witnesses that the section of `h_U` attached to its source is the restriction along `f` of the one
attached to its target. -/
lemma fiberSec_eq_of_isHomLift {V W : 𝒞} {x : (Over.forget U).Fiber V}
    {y : (Over.forget U).Fiber W} (f : V ⟶ W) (φ : x.1 ⟶ y.1)
    (hlift : (Over.forget U).IsHomLift f φ) : fiberSec x = f ≫ fiberSec y := by
  have hφ : φ.left = eqToHom x.2 ≫ f ≫ eqToHom y.2.symm := left_eq_of_isHomLift f φ hlift
  simp only [fiberSec, ← Over.w φ, hφ]
  simp

/-- Conversely, an equality of sections of `h_U` produces a morphism of `𝒞/U` over `f`. -/
def homOfFiberSec {V W : 𝒞} {x : (Over.forget U).Fiber V} {y : (Over.forget U).Fiber W}
    (f : V ⟶ W) (h : fiberSec x = f ≫ fiberSec y) : x.1 ⟶ y.1 :=
  Over.homMk (eqToHom x.2 ≫ f ≫ eqToHom y.2.symm) (by
    simp only [fiberSec] at h
    have hassoc : (eqToHom x.2 ≫ f ≫ eqToHom y.2.symm) ≫ y.1.hom
        = eqToHom x.2 ≫ f ≫ eqToHom y.2.symm ≫ y.1.hom := by simp
    rw [hassoc, ← h]
    simp)

/-- The morphism produced by `CategoryTheory.Over.homOfFiberSec` lies over the morphism of `𝒞`
along which the two sections of `h_U` were compared. -/
instance isHomLift_homOfFiberSec {V W : 𝒞} {x : (Over.forget U).Fiber V}
    {y : (Over.forget U).Fiber W} (f : V ⟶ W) (h : fiberSec x = f ≫ fiberSec y) :
    (Over.forget U).IsHomLift f (homOfFiberSec f h) :=
  (isHomLift_forget_iff _ f x.2 y.2).2 (by simp [homOfFiberSec])

/-- There is at most one morphism of `𝒞/U` over a given morphism of `𝒞` between two given
objects. -/
lemma hom_ext_of_isHomLift {A B : Over U} {V W : 𝒞} (f : V ⟶ W) {φ ψ : A ⟶ B}
    (hφ : (Over.forget U).IsHomLift f φ) (hψ : (Over.forget U).IsHomLift f ψ) : φ = ψ := by
  have := hφ
  exact (Over.forget U).map_injective
    ((left_eq_of_isHomLift f φ hφ).trans (left_eq_of_isHomLift f ψ hψ).symm)

/-- The fibre of `𝒞/U ⥤ 𝒞` over `V` is thin: its objects are the elements of `h_U(V)` and its
morphisms are the (unique) witnesses that two of them are equal. -/
instance fiber_hom_subsingleton {V : 𝒞} (x y : (Over.forget U).Fiber V) :
    Subsingleton (x ⟶ y) :=
  ⟨fun φ ψ ↦ Functor.Fiber.hom_ext (hom_ext_of_isHomLift (𝟙 V) φ.2 ψ.2)⟩

/-- Two objects of the fibre over `V` are connected by a morphism exactly when they are the same
element of `h_U(V)`. -/
lemma fiber_nonempty_hom_iff {V : 𝒞} (x y : (Over.forget U).Fiber V) :
    Nonempty (x ⟶ y) ↔ fiberSec x = fiberSec y := by
  refine ⟨fun ⟨φ⟩ ↦ ?_, fun h ↦ ⟨⟨homOfFiberSec (𝟙 V) (by simpa using h), inferInstance⟩⟩⟩
  simpa using fiberSec_eq_of_isHomLift (𝟙 V) φ.1 φ.2

/-- The object of the fibre of `𝒞/U ⥤ 𝒞` over `V` attached to a section `a : V ⟶ U` of `h_U`. -/
def fiberOfSec {V : 𝒞} (a : V ⟶ U) : (Over.forget U).Fiber V := ⟨Over.mk a, rfl⟩

/-- `CategoryTheory.Over.fiberOfSec` is a section of `CategoryTheory.Over.fiberSec`. -/
@[simp]
lemma fiberSec_fiberOfSec {V : 𝒞} (a : V ⟶ U) : fiberSec (fiberOfSec a) = a :=
  Category.id_comp a

/-- The chosen pullback of an object of a fibre of `𝒞/U ⥤ 𝒞` restricts its section of `h_U`. -/
lemma fiberSec_pullbackFiber {V W : 𝒞} (x : (Over.forget U).Fiber V) (f : W ⟶ V) :
    fiberSec (Functor.pullbackFiber (Over.forget U) x f) = f ≫ fiberSec x := by
  exact fiberSec_eq_of_isHomLift f (Functor.IsPreFibered.pullbackMap x.2 f) inferInstance

/-! ### The morphism presheaves of `𝒞/U ⥤ 𝒞` -/

/-- The presheaf `Mor(x, y)` of `𝒞/U ⥤ 𝒞` takes subsingleton values: the fibres of `𝒞/U ⥤ 𝒞`
are thin. -/
instance morPresheaf_subsingleton {V : 𝒞} (x y : (Over.forget U).Fiber V) (g : (Over V)ᵒᵖ) :
    Subsingleton ((Functor.morPresheaf (Over.forget U) x y).obj g) :=
  fiber_hom_subsingleton _ _

/-- `Mor(x, y)` has a section over `g : W ⟶ V` exactly when the elements of `h_U(V)` attached to
`x` and to `y` agree after restriction along `g`. -/
lemma morPresheaf_nonempty_iff {V : 𝒞} (x y : (Over.forget U).Fiber V) (g : Over V) :
    Nonempty ((Functor.morPresheaf (Over.forget U) x y).obj (op g)) ↔
      g.hom ≫ fiberSec x = g.hom ≫ fiberSec y := by
  rw [Functor.morPresheaf_obj, fiber_nonempty_hom_iff, fiberSec_pullbackFiber,
    fiberSec_pullbackFiber]

/-- When `h_U` is a sheaf, sections of `h_U` over `X.left` that agree on the members of a covering
sieve of `X : 𝒞/V` agree. -/
lemma comp_eq_of_locally_eq {J : GrothendieckTopology 𝒞}
    (hJ : Presieve.IsSheaf J (yoneda.obj U)) {V : 𝒞} {X : Over V} (S : Sieve X)
    (hS : S ∈ (J.over V) X) {a b : V ⟶ U}
    (h : ∀ ⦃Z : Over V⦄ ⦃k : Z ⟶ X⦄, S k → Z.hom ≫ a = Z.hom ≫ b) :
    X.hom ≫ a = X.hom ≫ b := by
  refine (hJ _ ((J.mem_over_iff S).1 hS)).isSeparatedFor.ext ?_
  intro Y k hk
  simpa using h ((Sieve.overEquiv_iff S k).1 hk)

/-- Condition (2) of Stacks 026F for `𝒞/U ⥤ 𝒞`: when `h_U` is a sheaf, each `Mor(x, y)` is a
sheaf. -/
lemma isMorSheaf_forget {J : GrothendieckTopology 𝒞} (hJ : Presieve.IsSheaf J (yoneda.obj U))
    (V : 𝒞) (x y : (Over.forget U).Fiber V) :
    Functor.IsMorSheaf (Over.forget U) J V x y := by
  refine (isSheaf_iff_isSheaf_of_type _ _).2 fun {X} S hS fam _ ↦ ?_
  obtain ⟨t⟩ : Nonempty ((Functor.morPresheaf (Over.forget U) x y).obj (op X)) :=
    (morPresheaf_nonempty_iff x y X).2
      (comp_eq_of_locally_eq hJ S hS fun {Z} {k} hk ↦
        (morPresheaf_nonempty_iff x y Z).1 ⟨fam k hk⟩)
  exact ⟨t, fun _ _ _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩

/-- Conversely, if the morphism presheaves of `𝒞/U ⥤ 𝒞` are sheaves then `h_U` is separated. -/
lemma isSeparatedFor_of_isMorSheaf {J : GrothendieckTopology 𝒞}
    (hmor : ∀ (V : 𝒞) (x y : (Over.forget U).Fiber V),
      Functor.IsMorSheaf (Over.forget U) J V x y)
    {V : 𝒞} (S : Sieve V) (hS : S ∈ J V) :
    Presieve.IsSeparatedFor (yoneda.obj U) (S : Presieve V) := by
  intro fam a b ha hb
  have hlocal : ∀ ⦃Y : 𝒞⦄ (k : Y ⟶ V), S k → k ≫ a = k ≫ b := fun {_} k hk ↦ by
    simpa using (ha k hk).trans (hb k hk).symm
  have hfam : ∀ ⦃Z : Over V⦄ ⦃k : Z ⟶ Over.mk (𝟙 V)⦄,
      ((Sieve.overEquiv (Over.mk (𝟙 V))).symm S) k →
        Z.hom ≫ fiberSec (fiberOfSec a) = Z.hom ≫ fiberSec (fiberOfSec b) := by
    intro Z k hk
    have hZ : Z.hom = k.left := by simpa using (Over.w k).symm
    simp only [fiberSec_fiberOfSec, hZ]
    exact hlocal k.left hk
  have famMor : Presieve.FamilyOfElements
      (Functor.morPresheaf (Over.forget U) (fiberOfSec a) (fiberOfSec b))
      (((Sieve.overEquiv (Over.mk (𝟙 V))).symm S : Sieve (Over.mk (𝟙 V))) :
        Presieve (Over.mk (𝟙 V))) :=
    fun {Z} k hk ↦ ((morPresheaf_nonempty_iff _ _ Z).2 (hfam hk)).some
  have hcompMor : famMor.Compatible := fun _ _ _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _
  obtain ⟨t, -⟩ := (isSheaf_iff_isSheaf_of_type _ _).1
    (hmor V (fiberOfSec a) (fiberOfSec b)) _
    (J.overEquiv_symm_mem_over (Over.mk (𝟙 V)) S hS) famMor hcompMor
  simpa using (morPresheaf_nonempty_iff (fiberOfSec a) (fiberOfSec b) (Over.mk (𝟙 V))).1 ⟨t⟩

/-! ### Descent data for `𝒞/U ⥤ 𝒞` -/

/-- Two objects of a fibre of `𝒞/U ⥤ 𝒞` carrying the same section of `h_U` are isomorphic in the
fibre. -/
def fiberIsoOfSecEq {V : 𝒞} {x y : (Over.forget U).Fiber V} (h : fiberSec x = fiberSec y) :
    x ≅ y where
  hom := ⟨homOfFiberSec (𝟙 V) (by simpa using h), inferInstance⟩
  inv := ⟨homOfFiberSec (𝟙 V) (by simpa using h.symm), inferInstance⟩
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- The descent datum for `𝒞/U ⥤ 𝒞` on a sieve `R` given by a compatible family of sections of
`h_U`, whose gluing isomorphisms are the unique witnesses that the restrictions of two members
agree. -/
noncomputable def sieveDescentDatumOfFamily {V : 𝒞} (R : Sieve V)
    (fam : Presieve.FamilyOfElements (yoneda.obj U) (R : Presieve V)) (hfam : fam.Compatible) :
    Functor.SieveDescentDatum (Over.forget U) R where
  obj {_} f hf := fiberOfSec (fam f hf)
  iso := by
    intro W₁ W₂ Z f hf g hg ε ε' heq
    refine fiberIsoOfSecEq ?_
    simp only [fiberSec_pullbackFiber, fiberSec_fiberOfSec]
    simpa using hfam ε ε' hf hg heq
  cocycle := by intros; exact Subsingleton.elim _ _
  iso_pullback := by intros; exact Subsingleton.elim _ _

/-- The family of sections of `h_U` underlying a descent datum for `𝒞/U ⥤ 𝒞`. -/
def famOfSieveDescentDatum {V : 𝒞} {R : Sieve V}
    (D : Functor.SieveDescentDatum (Over.forget U) R) :
    Presieve.FamilyOfElements (yoneda.obj U) (R : Presieve V) :=
  fun _ f hf ↦ fiberSec (D.obj f hf)

/-- The family of sections of `h_U` underlying a descent datum is compatible. -/
lemma famOfSieveDescentDatum_compatible {V : 𝒞} {R : Sieve V}
    (D : Functor.SieveDescentDatum (Over.forget U) R) :
    (famOfSieveDescentDatum D).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
  have h := (fiber_nonempty_hom_iff _ _).1 ⟨(D.iso h₁ h₂ g₁ g₂ hcomm).hom⟩
  rw [fiberSec_pullbackFiber, fiberSec_pullbackFiber] at h
  simpa [famOfSieveDescentDatum] using h

/-- Condition (3) of Stacks 026F for `𝒞/U ⥤ 𝒞`: when `h_U` is a sheaf, every descent datum for
`𝒞/U ⥤ 𝒞` is effective. -/
lemma hasEffectiveDescent_forget {J : GrothendieckTopology 𝒞}
    (hJ : Presieve.IsSheaf J (yoneda.obj U)) :
    Functor.HasEffectiveDescent (Over.forget U) J := by
  intro V R hR D
  obtain ⟨a, ha, -⟩ := hJ R hR _ (famOfSieveDescentDatum_compatible D)
  have hsec : ∀ ⦃W : 𝒞⦄ (f : W ⟶ V) (hf : R f),
      fiberSec (D.obj f hf) = f ≫ fiberSec (fiberOfSec a) := fun {_} f hf ↦ by
    simpa [famOfSieveDescentDatum] using (ha f hf).symm
  refine ⟨fiberOfSec a, fun {_} f hf ↦ homOfFiberSec f (hsec f hf), fun {_} f hf ↦ ?_, ?_⟩
  · have := isStronglyCartesian_forget f (homOfFiberSec f (hsec f hf))
    infer_instance
  · intro W₁ W₂ Z f hf g hg ε ε' heq
    refine hom_ext_of_isHomLift (ε' ≫ g) ?_ ?_
    · have hL : (Over.forget U).IsHomLift (𝟙 Z ≫ ε' ≫ g)
          (Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
            Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫
              homOfFiberSec g (hsec g hg)) := inferInstance
      simpa using hL
    · have hR' : (Over.forget U).IsHomLift (ε ≫ f)
          (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 ε ≫
            homOfFiberSec f (hsec f hf)) := inferInstance
      rwa [heq] at hR'

/-- Let `(𝒞, J)` be a site and let `U` be an object of `𝒞`. The localization `j_U : 𝒞/U ⥤ 𝒞` is a
stack over `𝒞` if and only if the representable presheaf `h_U` is a sheaf. -/
@[stacks 04WU]
theorem isStack_forget_iff_isSheaf (J : GrothendieckTopology 𝒞) :
    (Over.forget U).IsStack J ↔ Presheaf.IsSheaf J (yoneda.obj U) := by
  rw [isSheaf_iff_isSheaf_of_type]
  refine ⟨fun h {V} S hS fam hfam ↦ ?_,
    fun hJ ↦ ⟨isFibered_forget, isMorSheaf_forget hJ, hasEffectiveDescent_forget hJ⟩⟩
  obtain ⟨x, ζ, hcart, -⟩ := h.hasEffectiveDescent S hS (sieveDescentDatumOfFamily S fam hfam)
  have hamalg : fam.IsAmalgamation (fiberSec x) := fun {_} f hf ↦ by
    simpa [sieveDescentDatumOfFamily] using
      (fiberSec_eq_of_isHomLift f (ζ f hf) (hcart f hf).toIsHomLift).symm
  exact ⟨fiberSec x, hamalg,
    fun t ht ↦ isSeparatedFor_of_isMorSheaf h.isMorSheaf S hS fam t _ ht hamalg⟩

end Over

end CategoryTheory
