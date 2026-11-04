module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedSite

/-!
# Sections of a fibred category over the identity are cocontinuous

Let `p : C ⥤ D` be a fibred category over a site `(D, J)` and give `C` the topology inherited from
`J` (Stacks 06NV). A covering sieve `S` of an object `X` of `C` contains, over a `J`-covering
sieve of `p(X)`, the strongly cartesian lifts at `X` of the arrows of that sieve: the arrows
`g : V ⟶ p(X)` which have a strongly cartesian lift lying in `S` form a `J`-covering sieve,
`CategoryTheory.Functor.cartesianLiftSieve`.

Consequently every functor `σ : D ⥤ C` lying over the identity of `D` — sending each object `V`
to an object over `V` and each arrow to an arrow over it — is cocontinuous for the two
topologies: an arrow `σ(V') ⟶ σ(V)` over `g` factors through any strongly cartesian lift of `g`.
Restriction of presheaves along such a `σ` therefore preserves local surjectivity, local
injectivity and, where sheafification inverts exactly the locally bijective maps, the class of
maps inverted by sheafification.

The fibrewise point resolutions of Stacks 08VB are families of such functors
`V ↦ A_{n,V}`, and this is what lets the evaluation `V ↦ F(A_{n,V})` of a sheaf on `C` be
computed, after sheafification on `D`, from any presheaf whose sheafification is `F`.

## Main results

* `CategoryTheory.Functor.cartesianLiftSieve_mem`: the sieve of arrows with a strongly cartesian
  lift in an inherited covering sieve is a covering sieve.
* `CategoryTheory.Functor.isCocontinuous_of_isHomLift`: a functor lying over the identity is
  cocontinuous from `J` to the inherited topology.
* `CategoryTheory.Presheaf.W_whiskerLeft_of_isCocontinuous`: restriction along a cocontinuous
  functor preserves the maps inverted by sheafification, together with its local surjectivity and
  local injectivity halves.

## References

* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV)
* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] (p : C ⥤ D) [p.IsFibered]

/-- The arrows `g : V ⟶ p(X)` admitting a strongly cartesian lift at `X` which lies in a sieve
`S` of `X`. -/
def cartesianLiftSieve {X : C} (S : Sieve X) : Sieve (p.obj X) where
  arrows {_} g := ∃ (Y : C) (h : Y ⟶ X), p.IsStronglyCartesian g h ∧ S h
  downward_closed := by
    rintro V W g ⟨Y, h, hh, hS⟩ k
    obtain ⟨Z, k', hk'⟩ := IsPreFibered.exists_isCartesian p (IsHomLift.domain_eq p g h) k
    exact ⟨Z, k' ≫ h, inferInstance, S.downward_closed hS k'⟩

variable {p}

/-- Every arrow into `p(X)` has a strongly cartesian lift at `X`. -/
theorem exists_isStronglyCartesian {V : D} {X : C} (g : V ⟶ p.obj X) :
    ∃ (Y : C) (h : Y ⟶ X), p.IsStronglyCartesian g h := by
  obtain ⟨Y, h, hh⟩ := IsPreFibered.exists_isCartesian p (rfl : p.obj X = p.obj X) g
  exact ⟨Y, h, inferInstance⟩

omit [p.IsFibered] in
/-- An arrow over `g` factors through any strongly cartesian lift of `g` with the same target. -/
theorem exists_fac_of_isStronglyCartesian {V : D} {X Y Z : C} {g : V ⟶ p.obj X}
    (h : Y ⟶ X) [p.IsStronglyCartesian g h] (k : Z ⟶ X) [p.IsHomLift g k] :
    ∃ l : Z ⟶ Y, l ≫ h = k := by
  obtain ⟨l, ⟨-, hl⟩, -⟩ := IsStronglyCartesian.universal_property p g h (𝟙 V) g (by simp) k
  exact ⟨l, hl⟩

variable (p)

/-- **The cartesian lifts of an inherited covering sieve cover.** If `S` is a covering sieve of
`X` for the topology inherited from `J`, the arrows into `p(X)` with a strongly cartesian lift in
`S` form a `J`-covering sieve. -/
theorem cartesianLiftSieve_mem (J : GrothendieckTopology D) {X : C} {S : Sieve X}
    (hS : S ∈ p.inheritedTopology J X) : p.cartesianLiftSieve S ∈ J (p.obj X) := by
  change (p.inheritedPrecoverage J.toPrecoverage).Saturate X S at hS
  induction hS with
  | of X R hR =>
    obtain ⟨hcart, hmap⟩ := hR
    refine J.superset_covering ?_ hmap
    rintro V g ⟨W, a, b, hb, rfl⟩
    obtain ⟨Z, hZ, f, hf, hpf⟩ := Presieve.map_iff.mp hb
    have : p.IsStronglyCartesian (p.map f) f := hcart f hf
    have hg : a ≫ b = (a ≫ eqToHom hZ.symm) ≫ p.map f := by
      rw [hpf, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hg]
    obtain ⟨Y, a', ha'⟩ := IsPreFibered.exists_isCartesian p (rfl : p.obj Z = p.obj Z)
      (a ≫ eqToHom hZ.symm)
    exact ⟨Y, a' ≫ f, inferInstance, Sieve.downward_closed _ (Sieve.le_generate R _ f hf) a'⟩
  | top X =>
    refine J.superset_covering (fun V g _ => ?_) (J.top_mem _)
    obtain ⟨Y, h, hh⟩ := exists_isStronglyCartesian (p := p) g
    exact ⟨Y, h, hh, trivial⟩
  | pullback X S _ Y f ih =>
    refine J.superset_covering ?_ (J.pullback_stable (p.map f) ih)
    rintro V g ⟨Z, h, hh, hS⟩
    obtain ⟨Y', g', hg'⟩ := exists_isStronglyCartesian (p := p) g
    obtain ⟨l, hl⟩ := exists_fac_of_isStronglyCartesian (g := g ≫ p.map f) h (g' ≫ f)
    refine ⟨Y', g', hg', ?_⟩
    change S (g' ≫ f)
    exact hl ▸ S.downward_closed hS l
  | transitive X S R _ _ ihS ihR =>
    refine J.transitive ihS _ ?_
    rintro V g ⟨Y, h, hh, hS⟩
    obtain rfl : p.obj Y = V := IsHomLift.domain_eq p g h
    refine J.superset_covering ?_ (ihR hS)
    rintro W k ⟨Z, k', hk', hR⟩
    exact ⟨Z, k' ≫ h, inferInstance, hR⟩

/-- **A functor lying over the identity of the base is cocontinuous.** Let `σ : D ⥤ C` send each
object `V` to an object over `V` and each arrow `g` to an arrow over `g`. Then `σ` is cocontinuous
from `J` to the topology inherited from `J`: for a covering sieve `S` of `σ(V)`, an arrow
`g : V' ⟶ V` whose cartesian lift lies in `S` has `σ(g)` in `S`, since `σ(g)` factors through that
lift. -/
theorem isCocontinuous_of_isHomLift (J : GrothendieckTopology D) (σ : D ⥤ C)
    (hobj : ∀ V, p.obj (σ.obj V) = V) (hmap : ∀ {V W : D} (g : V ⟶ W), p.IsHomLift g (σ.map g)) :
    σ.IsCocontinuous J (p.inheritedTopology J) where
  cover_lift {V S} hS := by
    refine J.superset_covering ?_
      (J.pullback_stable (eqToHom (hobj V).symm) (p.cartesianLiftSieve_mem J hS))
    rintro V' g ⟨Y, h, hh, hSh⟩
    have := hmap g
    have : p.IsHomLift (g ≫ eqToHom (hobj V).symm) (σ.map g) :=
      IsHomLift.of_fac' p _ _ (hobj V') rfl (by simpa using IsHomLift.fac' p g (σ.map g))
    obtain ⟨l, hl⟩ := exists_fac_of_isStronglyCartesian (g := g ≫ eqToHom (hobj V).symm) h
      (σ.map g)
    change S (σ.map g)
    exact hl ▸ S.downward_closed hSh l

end CategoryTheory.Functor

namespace CategoryTheory.Presheaf

variable {C D : Type*} [Category* C] [Category* D] {J : GrothendieckTopology D}
  {K : GrothendieckTopology C} (σ : D ⥤ C) [σ.IsCocontinuous J K]
  {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- Restriction of presheaves along a cocontinuous functor preserves local surjectivity. -/
theorem isLocallySurjective_whiskerLeft_of_isCocontinuous {F G : Cᵒᵖ ⥤ A} (φ : F ⟶ G)
    [IsLocallySurjective K φ] : IsLocallySurjective J (Functor.whiskerLeft σ.op φ) where
  imageSieve_mem {V} s :=
    J.superset_covering (fun _ _ h => h) (σ.cover_lift J K (imageSieve_mem K φ (U := op (σ.obj V))
      s))

/-- Restriction of presheaves along a cocontinuous functor preserves local injectivity. -/
theorem isLocallyInjective_whiskerLeft_of_isCocontinuous {F G : Cᵒᵖ ⥤ A} (φ : F ⟶ G)
    [IsLocallyInjective K φ] : IsLocallyInjective J (Functor.whiskerLeft σ.op φ) where
  equalizerSieve_mem {V} x y h :=
    J.superset_covering (fun _ _ h => h) (σ.cover_lift J K (equalizerSieve_mem K φ
      (X := op (σ.obj V.unop)) x y h))

/-- Restriction of presheaves along a cocontinuous functor preserves the maps inverted by
sheafification, for values in which sheafification inverts exactly the locally bijective maps. -/
theorem W_whiskerLeft_of_isCocontinuous [J.WEqualsLocallyBijective A]
    [K.WEqualsLocallyBijective A] {F G : Cᵒᵖ ⥤ A} {φ : F ⟶ G} (hφ : K.W φ) :
    J.W (Functor.whiskerLeft σ.op φ) := by
  have := GrothendieckTopology.W.isLocallyInjective (J := K) hφ
  have := GrothendieckTopology.W.isLocallySurjective (J := K) hφ
  have := isLocallyInjective_whiskerLeft_of_isCocontinuous (J := J) (K := K) σ φ
  have := isLocallySurjective_whiskerLeft_of_isCocontinuous (J := J) (K := K) σ φ
  exact J.W_of_isLocallyBijective _

end CategoryTheory.Presheaf
