module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.Completed.InverseLimit
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.FormalObject.Filtration
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts
public import StacksFrontier.Deformation.Schlessinger.Basic
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.Deformation.VersalObject.Descent
public import StacksFrontier.Deformation.VersalObject.MinimalDescent

/-!
# Tools for minimal descent objects

Elementary facts used throughout the construction of the smallest base of a versal formal object:
a morphism of `𝒞_Λ` is an isomorphism exactly when it is bijective, two injective morphisms into
the same object with the same range have isomorphic sources, and minimality of a descent object
therefore depends only on the subalgebra it cuts out. The file also records that minimality forces
every incoming arrow to be surjective on bases.

## Main definitions

* `Deformation.ArtinianLocalAlgCat.isoOfRangeEq`: two injective morphisms of `𝒞_Λ` into the same
  object with the same range have isomorphic sources: the isomorphism is the comparison of the two
  subalgebras they describe.
* `Deformation.identityDescent`: the identity arrow of `x`, regarded as the largest descent object
  of `x`.

## Main results

* `Deformation.artinianHom_surjective_of_isIso`: an isomorphism of `𝒞_Λ` is surjective on
  underlying algebras.
* `Deformation.artinianHom_injective_of_isIso`: an isomorphism of `𝒞_Λ` is injective on underlying
  algebras.
* `Deformation.algHom_range_comp_eq_of_surjective`: precomposition with a surjection does not
  change the range of an algebra homomorphism.
* `Deformation.algHom_range_eq_of_isHomLift`: a morphism of the base lifted by a morphism `φ` of
  the total category has the same range as the image of `φ`.
* `Deformation.map_isIso_of_isHomLift_isIso`: a morphism of the total category lying over an
  isomorphism has an isomorphism for image.
* `Deformation.map_surjective_of_isHomLift_surjective`: a morphism of the total category lying
  over a surjection has a surjective image.
* `Deformation.ArtinianLocalAlgCat.isoOfRangeEq_hom_fac`: the comparison isomorphism of two
  subalgebras with the same range commutes with their inclusions.
* `Deformation.isMinimal_of_iso`: minimality of an object is invariant under isomorphism.
* `Deformation.minimalDescent_iso_of_same_image`: minimality of a descent object depends only on
  the subalgebra it describes: if two commuting arrows into `x` cut out the same image subalgebra
  and one is minimal, so is the other.
* `Deformation.artinianHom_bijective_of_injective_field_target`: an injective morphism of `𝒞_Λ`
  whose target has vanishing maximal ideal is bijective.
* `Deformation.level_zero_maximalIdeal_eq_bot`: the zeroth level of a formal object lies over the
  residue field, so its maximal ideal vanishes.
* `Deformation.stronglyCocartesian_postcomp_iso`: postcomposing a strongly cocartesian morphism
  with an isomorphism lying over an identity again gives a strongly cocartesian morphism.
* `Deformation.identityDescent_isMinimal`: over an object with vanishing maximal ideal the
  identity descent object is minimal.
* `Deformation.descentPushforward_inclusion_surjective`: the comparison arrow of a specified
  descent pushforward is surjective on bases, since the output subalgebra is the image of the input
  one.
* `Deformation.minimalDescent_map_surjective`: an arrow from `y` into a minimal descent object of
  `y` is surjective on bases.
* `Deformation.map_surjective_into_minimalDescent`: any arrow into a minimal descent object is
  surjective on bases.
* `Deformation.formal_transition_surjective`: the transition morphisms of a formal object are
  surjective on bases.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- An isomorphism of `𝒞_Λ` is surjective on underlying algebras. -/
alias artinianHom_surjective_of_isIso := surjective_hom_of_isIso

/-- An isomorphism of `𝒞_Λ` is injective on underlying algebras. -/
theorem artinianHom_injective_of_isIso
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B) [IsIso f] :
  Function.Injective f.hom := by
  intro a b hab
  simpa only [← AlgHom.comp_apply, ← ArtinianLocalAlgCat.comp_hom,
    IsIso.hom_inv_id, ArtinianLocalAlgCat.id_hom, AlgHom.id_apply] using congrArg (inv f).hom hab


/-- Precomposition with a surjection does not change the range of an algebra homomorphism. -/
theorem algHom_range_comp_eq_of_surjective
    {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (hf : Function.Surjective f) : (g.comp f).range = g.range := by
  rw [AlgHom.range_comp, (AlgHom.range_eq_top _).mpr hf, Algebra.map_top]


/-- A morphism of the base lifted by a morphism `φ` of the total category has the same range as the
image of `φ`. -/
theorem algHom_range_eq_of_isHomLift
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k} {x y : F}
    (f : A ⟶ p.obj y) (φ : x ⟶ y) (hf : p.IsHomLift f φ) :
    f.hom.range = (p.map φ).hom.range := by
  obtain rfl := IsHomLift.domain_eq p f φ
  rw [IsHomLift.eq_of_isHomLift p f φ]

/-- A morphism of the total category lying over an isomorphism has an isomorphism for image. -/
theorem map_isIso_of_isHomLift_isIso
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} {x y : F}
    (f : A ⟶ B) (φ : x ⟶ y) (hf : IsIso f)
    (h : p.IsHomLift f φ) : IsIso (p.map φ) := by
  subst_hom_lift p f φ
  exact hf

/-- A morphism of the total category lying over a surjection has a surjective image. -/
theorem map_surjective_of_isHomLift_surjective
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} {x y : F}
    (f : A ⟶ B) (φ : x ⟶ y) (hf : Function.Surjective f.hom)
    (h : p.IsHomLift f φ) : Function.Surjective (p.map φ).hom := by
  subst_hom_lift p f φ
  exact hf


/-- A factorisation `e ≫ g = f` of injective morphisms of `𝒞_Λ`, with a factorisation back
`e' ≫ f = g`, makes `e` an isomorphism. -/
private theorem isIso_of_comp_eq_of_injective
    {A B C : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ C) (g : B ⟶ C)
    (e : A ⟶ B) (e' : B ⟶ A) (he : e ≫ g = f) (he' : e' ≫ f = g)
    (hf : Function.Injective f.hom) (hg : Function.Injective g.hom) : IsIso e := by
  have h (a : A) : g.hom (e.hom a) = f.hom a := by rw [← he]; rfl
  have h' (b : B) : f.hom (e'.hom b) = g.hom b := by rw [← he']; rfl
  refine ArtinianLocalAlgCat.isIso_of_bijective_hom e
    ⟨fun a b hab ↦ hf ?_, fun b ↦ ⟨e'.hom b, hg ?_⟩⟩
  · rw [← h, ← h, hab]
  · rw [h, h']

/-- Two injective morphisms of `𝒞_Λ` into the same object with the same range have isomorphic
sources: the isomorphism is the comparison of the two subalgebras they describe. -/
noncomputable def ArtinianLocalAlgCat.isoOfRangeEq
    {A B C : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : A ⟶ C) (g : B ⟶ C)
    (hf : Function.Injective f.hom) (hg : Function.Injective g.hom)
    (hrange : AlgHom.range f.hom = AlgHom.range g.hom) : A ≅ B := by
  let e := Classical.choose
    (ArtinianLocalAlgCat.exists_factor_of_range_le f g hg (le_of_eq hrange))
  have he := Classical.choose_spec
    (ArtinianLocalAlgCat.exists_factor_of_range_le f g hg (le_of_eq hrange))
  let e' := Classical.choose
    (ArtinianLocalAlgCat.exists_factor_of_range_le g f hf (le_of_eq hrange.symm))
  have he' := Classical.choose_spec
    (ArtinianLocalAlgCat.exists_factor_of_range_le g f hf (le_of_eq hrange.symm))
  have hefun (a : A) : g.hom (e.hom a) = f.hom a := by
    simpa only [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply] using
      congrArg (fun t : A ⟶ C => t.hom a) he
  have he'fun (b : B) : f.hom (e'.hom b) = g.hom b := by
    simpa only [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply] using
      congrArg (fun t : B ⟶ C => t.hom b) he'
  haveI : IsIso e := by
    apply ArtinianLocalAlgCat.isIso_of_bijective_hom e
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply hf
      calc
        f.hom a = g.hom (e.hom a) := (hefun a).symm
        _ = g.hom (e.hom b) := congrArg g.hom hab
        _ = f.hom b := hefun b
    · intro b
      refine ⟨e'.hom b, ?_⟩
      apply hg
      calc
        g.hom (e.hom (e'.hom b)) = f.hom (e'.hom b) := hefun _
        _ = g.hom b := he'fun b
  exact asIso e

/-- The comparison isomorphism of two subalgebras with the same range commutes with their
inclusions. -/
theorem ArtinianLocalAlgCat.isoOfRangeEq_hom_fac
    {A B C : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : A ⟶ C) (g : B ⟶ C)
    (hf : Function.Injective f.hom) (hg : Function.Injective g.hom)
    (hrange : AlgHom.range f.hom = AlgHom.range g.hom) :
    (ArtinianLocalAlgCat.isoOfRangeEq f g hf hg hrange).hom ≫ g = f := by
  change Classical.choose
    (ArtinianLocalAlgCat.exists_factor_of_range_le f g hg (le_of_eq hrange)) ≫ g = f
  exact Classical.choose_spec
    (ArtinianLocalAlgCat.exists_factor_of_range_le f g hg (le_of_eq hrange))

/-- Minimality of an object is invariant under isomorphism. -/
theorem isMinimal_of_iso
    {C : Type*} [Category C] {X Y : C} (e : X ≅ Y)
    (hY : IsMinimalObject Y) : IsMinimalObject X := by
  intro Z f
  have : IsIso (f ≫ e.hom) := hY Z (f ≫ e.hom)
  have : IsIso f := by
    rw [show f = (f ≫ e.hom) ≫ e.inv by simp]
    infer_instance
  infer_instance

/-- Minimality of a descent object depends only on the subalgebra it describes: if two commuting
arrows into `x` cut out the same image subalgebra and one is minimal, so is the other. -/
theorem minimalDescent_iso_of_same_image
    (hp : IsCofiberedInGroupoids p)
    {z y w x : F} (k : z ⟶ y) (i : z ⟶ w) (g : y ⟶ x) (v : w ⟶ x)
    (hcomm : k ≫ g = i ≫ v)
    (hg : Function.Injective (p.map g).hom)
    (hv : Function.Injective (p.map v).hom)
    (hRangeG : AlgHom.range (p.map g).hom =
      AlgHom.range ((p.map k ≫ p.map g).hom))
    (hRangeV : AlgHom.range (p.map v).hom =
      AlgHom.range ((p.map i ≫ p.map v).hom))
    (hmin : IsMinimalObject (⟨Over.mk v, hv⟩ : DescentObject p x)) :
    IsMinimalObject (⟨Over.mk g, hg⟩ : DescentObject p x) := by
  have hcomp : p.map k ≫ p.map g = p.map i ≫ p.map v := by
    rw [← p.map_comp, ← p.map_comp, hcomm]
  have hRange : AlgHom.range (p.map g).hom = AlgHom.range (p.map v).hom := by
    rw [hRangeG, hcomp, ← hRangeV]
  obtain ⟨e, he⟩ := ArtinianLocalAlgCat.exists_factor_of_range_le (p.map g) (p.map v) hv
    (le_of_eq hRange)
  obtain ⟨e', he'⟩ := ArtinianLocalAlgCat.exists_factor_of_range_le (p.map v) (p.map g) hg
    (le_of_eq hRange.symm)
  have : Mono (p.map v) := ⟨fun _ _ h ↦ ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun a ↦
    hv (DFunLike.congr_fun (congrArg ArtinianLocalAlgCat.Hom.hom h) a))⟩
  have : IsIso e := isIso_of_comp_eq_of_injective _ _ e e' he he' hg hv
  obtain ⟨r, ⟨hrmap, hrfac⟩, _⟩ := existsUnique_factor_of_isHomLift hp k i e
    ((cancel_mono (p.map v)).1 (by rw [Category.assoc, he, hcomp]))
  have : IsIso (p.map r) := by rw [hrmap]; infer_instance
  have : IsIso r := isIso_of_isIso_map hp r
  have hrv : r ≫ v = g := by
    obtain ⟨t, ⟨ht, htfac⟩, huniq⟩ := existsUnique_factor_of_isHomLift hp k (k ≫ g) (p.map g) (by
      rw [p.map_comp])
    have hr : p.map (r ≫ v) = p.map g := by rw [p.map_comp, hrmap, he]
    have hrfac' : k ≫ (r ≫ v) = k ≫ g := by rw [← Category.assoc, hrfac, hcomm]
    exact (huniq (r ≫ v) ⟨hr, hrfac'⟩).trans (huniq g ⟨rfl, rfl⟩).symm
  let rIso : Over.mk g ≅ Over.mk v := Over.isoMk (asIso r) hrv
  let eIso : (⟨Over.mk g, hg⟩ : DescentObject p x) ≅
      (⟨Over.mk v, hv⟩ : DescentObject p x) := ObjectProperty.isoMk _ rIso
  exact isMinimal_of_iso eIso hmin

/-- An injective morphism of `𝒞_Λ` whose target has vanishing maximal ideal is bijective. -/
theorem artinianHom_bijective_of_injective_field_target
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B)
    (hmax : maximalIdeal B = ⊥)
    (hf : Function.Injective f.hom) : Function.Bijective f.hom := by
  refine ⟨hf, fun b ↦ ?_⟩
  obtain ⟨a, ha⟩ := residue_surjective (A.residueEquiv.symm (B.residueEquiv (residue B b)))
  refine ⟨a, ?_⟩
  have hres : residue B (f.hom a) = residue B b := by
    apply B.residueEquiv.injective
    rw [f.residue_comm a, ha, A.residueEquiv.apply_symm_apply]
  have hker : f.hom a - b ∈ maximalIdeal B :=
    (residue_eq_zero_iff _).mp (by rw [map_sub, hres, sub_self])
  rw [hmax] at hker
  exact sub_eq_zero.mp (Ideal.mem_bot.mp hker)

/-- The zeroth level of a formal object lies over the residue field, so its maximal ideal vanishes.
-/
theorem level_zero_maximalIdeal_eq_bot (ξ : FormalObject p) :
    maximalIdeal (p.obj (ξ.level 0)) = ⊥ := by
  rw [ξ.level_eq 0]
  change maximalIdeal (AdicTruncation.obj ξ.base 0) = ⊥
  let q : ξ.base →+* AdicTruncation.obj ξ.base 0 :=
    Ideal.Quotient.mk (AdicTruncation.ideal ξ.base 0)
  rw [← IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective]
  change Ideal.map (Ideal.Quotient.mk (maximalIdeal ξ.base ^ (0 + 1)))
    (maximalIdeal ξ.base) = ⊥
  refine le_antisymm ?_ bot_le
  rw [Ideal.map_le_iff_le_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, pow_one]

/-- Postcomposing a strongly cocartesian morphism with an isomorphism lying over an identity again
gives a strongly cocartesian morphism. -/
theorem stronglyCocartesian_postcomp_iso
    {C : Type u} [Category.{v} C] {G : Type uF} [Category.{vF} G]
    (q : G ⥤ C) {R S : C} {a b c : G} (f : R ⟶ S) (φ : a ⟶ b)
    [q.IsStronglyCocartesian f φ] (e : b ≅ c)
    [q.IsHomLift (𝟙 S) e.hom] : q.IsStronglyCocartesian f (φ ≫ e.hom) := by
  have hφ : q.IsHomLift f (φ ≫ e.hom) := by
    let : q.IsHomLift (𝟙 S) e.hom := inferInstance
    let : q.IsHomLift f φ := inferInstance
    infer_instance
  let := hφ
  refine { universal_property' := ?_ }
  intro z g ψ
  intro hψ
  let : q.IsHomLift (f ≫ g) ψ := hψ
  obtain ⟨χ, hχ, huniq⟩ :=
    Functor.IsStronglyCocartesian.universal_property q f φ g (f ≫ g) rfl ψ
  refine ⟨e.inv ≫ χ, ⟨?_, ?_⟩, ?_⟩
  · have hinv : q.IsHomLift (𝟙 S) e.inv := IsHomLift.lift_id_inv q S e
    let := hinv
    let := hχ.1
    infer_instance
  · simp [Category.assoc, hχ.2]
  · intro χ' hχ'
    have hmidlift : q.IsHomLift g (e.hom ≫ χ') := by
      let := hχ'.1
      let : q.IsHomLift (𝟙 S) e.hom := inferInstance
      infer_instance
    rw [← huniq (e.hom ≫ χ') ⟨hmidlift, (Category.assoc _ _ _).symm.trans hχ'.2⟩,
      Iso.inv_hom_id_assoc]

/-- The identity arrow of `x`, regarded as the largest descent object of `x`. -/
abbrev identityDescent (x : F) : DescentObject p x :=
  ⟨Over.mk (𝟙 x), by
    change Function.Injective (p.map (𝟙 x)).hom
    rw [p.map_id, ArtinianLocalAlgCat.id_hom]
    exact Function.injective_id⟩

/-- Over an object with vanishing maximal ideal the identity descent object is minimal. -/
theorem identityDescent_isMinimal
    (hp : IsCofiberedInGroupoids p) (x : F)
    (hmax : maximalIdeal (p.obj x) = ⊥) : IsMinimalObject (identityDescent (p := p) x) := by
  intro Y f
  have hfac : f.hom.left = Y.1.hom := by simpa [identityDescent] using Over.w f.hom
  have : IsIso (p.map f.hom.left) := ArtinianLocalAlgCat.isIso_of_bijective_hom _
    (artinianHom_bijective_of_injective_field_target (p.map f.hom.left) hmax (hfac ▸ Y.2))
  have : IsIso f.hom.left := isIso_of_isIso_map hp _
  let e : Y ≅ identityDescent (p := p) x := ObjectProperty.isoMk _
    (Over.isoMk (asIso f.hom.left) (by dsimp [identityDescent]; simpa using hfac))
  exact (ObjectProperty.hom_ext _ (Over.OverMorphism.ext rfl) : f = e.hom) ▸ Iso.isIso_hom e

/-- The comparison arrow of a specified descent pushforward is surjective on bases, since the
output subalgebra is the image of the input one. -/
theorem descentPushforward_inclusion_surjective
    {y x : F} (g : y ⟶ x)
    (D : DescentPushforward p g) (X : DescentObject p y) :
    Function.Surjective (p.map (D.inclusion X)).hom := by
  intro b
  obtain ⟨a, ha⟩ : (p.map (D.functor.obj X).obj.hom).hom b ∈
      AlgHom.range (p.map (X.obj.hom ≫ g)).hom :=
    D.base_range X ▸ ⟨b, rfl⟩
  refine ⟨a, (D.functor.obj X).property ?_⟩
  rw [← ha, ← D.inclusion_fac X, Functor.map_comp, ArtinianLocalAlgCat.comp_hom]
  rfl

/-- An arrow from `y` into a minimal descent object of `y` is surjective on bases. -/
theorem minimalDescent_map_surjective
    (hp : IsCofiberedInGroupoids p)
    {y : F} (X : DescentObject p y) (hX : IsMinimalObject X)
    (f : y ⟶ X.obj.left) :
    Function.Surjective (p.map f).hom := by
  let D := descentPushforward p hp f
  let I := identityDescent (p := p) y
  let Z₀ := D.functor.obj I
  let j := Z₀.obj.hom
  let Z : DescentObject p y := ⟨Over.mk (j ≫ X.obj.hom), by
    change Function.Injective (p.map (j ≫ X.obj.hom)).hom
    rw [Functor.map_comp]
    exact X.property.comp Z₀.property⟩
  let m : Z ⟶ X := ObjectProperty.homMk (Over.homMk j (by rfl))
  have : IsIso m.hom := (ObjectProperty.isIso_hom_iff m).mpr (hX Z m)
  have : IsIso j := Functor.map_isIso (Over.forget y) m.hom
  rw [← AlgHom.range_eq_top, ← Category.id_comp f]
  exact (D.base_range I).symm.trans
    ((AlgHom.range_eq_top _).mpr (artinianHom_surjective_of_isIso (p.map j)))

/-- Any arrow into a minimal descent object is surjective on bases. -/
theorem map_surjective_into_minimalDescent
    (hp : IsCofiberedInGroupoids p)
    {x : F} (X : DescentObject p x) (hX : IsMinimalObject X)
    {z : F} (f : z ⟶ X.obj.left) :
    Function.Surjective (p.map f).hom := by
  let D := descentPushforward p hp f
  let I := identityDescent (p := p) z
  let W := D.functor.obj I
  let v := W.obj.hom
  let Z : DescentObject p x := ⟨Over.mk (v ≫ X.obj.hom), by
    change Function.Injective (p.map (v ≫ X.obj.hom)).hom
    rw [Functor.map_comp]
    exact X.property.comp W.property⟩
  let m : Z ⟶ X := ObjectProperty.homMk (Over.homMk v (by rfl))
  have : IsIso m.hom := (ObjectProperty.isIso_hom_iff m).mpr (hX Z m)
  have : IsIso v := Functor.map_isIso (Over.forget x) m.hom
  rw [← show D.inclusion I ≫ v = f by simpa [v, I, identityDescent] using D.inclusion_fac I,
    Functor.map_comp]
  exact (artinianHom_surjective_of_isIso (p.map v)).comp
    (descentPushforward_inclusion_surjective f D I)

/-- The transition morphisms of a formal object are surjective on bases. -/
theorem formal_transition_surjective (ξ : FormalObject p) (n : ℕ) :
    Function.Surjective (p.map (ξ.transition n)).hom := by
  refine map_surjective_of_isHomLift_surjective _ _ ?_ (ξ.transition_lift n)
  change Function.Surjective (AdicTruncation.transition ξ.base n).hom
  unfold AdicTruncation.transition
  exact Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

end Deformation

end
