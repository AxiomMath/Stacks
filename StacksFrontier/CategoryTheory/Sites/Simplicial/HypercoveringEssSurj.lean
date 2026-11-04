module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringRigid
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalFibrewise

/-!
# Every cartesian sheaf on the total site of a hypercovering is an inverse image

Let `(C, J)` be a site with equalizers and fibre products and let `K` be a hypercovering of the
final presheaf. This file proves the following part of Stacks 0D8E (1): a cartesian sheaf of sets
on the total site `(C/K)_total` lies in the essential image of restriction along the localization
functor `j_total`.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.ranSection` and `.ranPresheaf`: the right Kan
  extension of a presheaf on the total site along `j_total`, written out by hand.
* `CategoryTheory.SimplicialSemiRepresentable.ranEv`: the comparison morphism from the
  restriction of that Kan extension back to the original presheaf.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.isSheaf_ranPresheaf`: the Kan extension of a sheaf
  is a sheaf.
* `CategoryTheory.SimplicialSemiRepresentable.essImage_of_rigid`: a sheaf on the total site which
  inverts the arrows lying over isomorphisms of `C`, and on which restriction depends only on the
  image of the arrow in `C`, is an inverse image along `j_total`.
* `CategoryTheory.SimplicialSemiRepresentable.essImage_of_isCartesianSheaf`: **Stacks 0D8E (1)**,
  essential surjectivity of `a⁻¹` onto the cartesian sheaves of sets.
* `CategoryTheory.SimplicialSemiRepresentable.mem_essImage_iff_isCartesianSheaf'` and
  `.isIso_counit_app_hypercovering'`: **Stacks 0D8E (1)**, the essential image of `a⁻¹` is exactly
  the cartesian sheaves of sets, and the counit `a⁻¹ a_* F ⟶ F` is invertible on them.

## Implementation notes

The two inputs beyond the degree-zero condition are local fullness of `j_total`, which is
`CategoryTheory.SimplicialSemiRepresentable.isLocallyFull_totalForget`, and the *rigidity* of a
cartesian sheaf — restriction along an arrow of the total site depends only on the image of that
arrow in `C` — which is
`CategoryTheory.SimplicialSemiRepresentable.map_eq_of_totalForget_map_eq`.

A section of the Kan extension over `j_total(W₀)` is reconstructed from its value at the identity
chart by the *local values* of that value: `IsLocalValue σ W φ t` says that `t` restricts to `σ`
along every pair of arrows of the total site lying over `φ`. Rigidity makes a local value
independent of the chosen lift, local fullness makes lifts exist locally, and cocontinuity of
`j_total` turns a covering sieve of `C` into one of the total topology, along which the local
values are glued.

The Kan extension is written out rather than taken from Mathlib: a section of it over `X` is a
family of sections of `F` over the objects of the total site charted over `X`, compatible with
every arrow of the total site.

## References

* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable SimplicialSiteSituation

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]
  (F : Sheaf (situation J K).totalTopology (Type u))

/-! ### The right Kan extension along `j_total`, written out -/

/-- A section over `X : C` of the right Kan extension of `F` along `j_total`: a section of `F`
over every object of the total site charted over `X`, compatibly with every arrow of the total
site. -/
def ranSection (X : C) : Type u :=
  { s : ∀ W : Grothendieck (slices K), ((totalForget K).obj W ⟶ X) → F.obj.obj (op W) //
    ∀ {W W' : Grothendieck (slices K)} (θ : W' ⟶ W) (φ : (totalForget K).obj W ⟶ X),
      F.obj.map θ.op (s W φ) = s W' ((totalForget K).map θ ≫ φ) }

/-- The right Kan extension of `F` along `j_total`, as a presheaf on `C`. -/
def ranPresheaf : Cᵒᵖ ⥤ Type u where
  obj X := ranSection J K F X.unop
  map {_ _} f := ↾fun s => ⟨fun W φ => s.1 W (φ ≫ f.unop), fun {_ _} θ φ =>
    (s.2 θ (φ ≫ f.unop)).trans (congrArg (s.1 _) (Category.assoc _ _ _).symm)⟩
  map_id _ := ConcreteCategory.hom_ext _ _ fun s =>
    Subtype.ext (funext fun W => funext fun φ => congrArg (s.1 W) (Category.comp_id φ))
  map_comp _ _ := ConcreteCategory.hom_ext _ _ fun s =>
    Subtype.ext (funext fun W => funext fun _ => congrArg (s.1 W) (Category.assoc _ _ _).symm)

/-- Restriction in the Kan extension precomposes the charts. -/
theorem ranPresheaf_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : (ranPresheaf J K F).obj X)
    (W : Grothendieck (slices K)) (φ : (totalForget K).obj W ⟶ Y.unop) :
    ((ranPresheaf J K F).map f s).1 W φ = s.1 W (φ ≫ f.unop) :=
  rfl

/-- Two sections of the Kan extension agree as soon as all their values agree. -/
theorem ranSection_ext {X : C} {s t : ranSection J K F X}
    (h : ∀ (W : Grothendieck (slices K)) (φ : (totalForget K).obj W ⟶ X), s.1 W φ = t.1 W φ) :
    s = t :=
  Subtype.ext (funext fun W => funext fun φ => h W φ)

/-- Restriction along a composite of arrows of the total site, on an element. -/
theorem map_comp_apply {W W' W'' : Grothendieck (slices K)} (ρ : W'' ⟶ W') (θ : W' ⟶ W)
    (t : F.obj.obj (op W)) :
    F.obj.map (ρ ≫ θ).op t = F.obj.map ρ.op (F.obj.map θ.op t) :=
  ConcreteCategory.congr_hom (F.obj.map_comp θ.op ρ.op) t

/-- Composing a chart with a composite of arrows of the total site reassociates. -/
private theorem totalForget_map_comp_comp {W W' W'' : Grothendieck (slices K)} (ρ : W'' ⟶ W')
    (θ : W' ⟶ W) {X : C} (φ : (totalForget K).obj W ⟶ X) :
    (totalForget K).map (ρ ≫ θ) ≫ φ = (totalForget K).map ρ ≫ ((totalForget K).map θ ≫ φ) := by
  simp

/-! ### The Kan extension of a sheaf is a sheaf -/

/-- **The right Kan extension of a sheaf on the total site along `j_total` is a sheaf.** -/
theorem isSheaf_ranPresheaf : Presheaf.IsSheaf J (ranPresheaf J K F) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X R hR xx hxx
  have hxs := hxx.to_sieveCompatible
  have hxc : ∀ {Y : C} {f f' : Y ⟶ X} (hf : R f) (hf' : R f') (_ : f = f'),
      xx f hf = xx f' hf' := by
    intro Y f f' hf hf' h
    subst h
    rfl
  have hev : ∀ {W : Grothendieck (slices K)} {z z' : ranSection J K F ((totalForget K).obj W)},
      z = z' → z.1 W (𝟙 _) = z'.1 W (𝟙 _) := fun h => congrArg (fun z => z.1 _ (𝟙 _)) h
  have hres : ∀ {X' : C} (z : ranSection J K F X') {W : Grothendieck (slices K)}
      (χ : (totalForget K).obj W ⟶ X'), z.1 W χ = ((ranPresheaf J K F).map χ.op z).1 W (𝟙 _) :=
    fun z _ χ => congrArg (z.1 _) (Category.id_comp χ).symm
  have hcov : ∀ (W : Grothendieck (slices K)) (φ : (totalForget K).obj W ⟶ X),
      Sieve.functorPullback (totalForget K) (R.pullback φ) ∈ (situation J K).totalTopology W :=
    fun W φ => functorPullback_mem_totalTopology K J W _ (J.pullback_stable φ hR)
  have main : ∀ (W : Grothendieck (slices K)) (φ : (totalForget K).obj W ⟶ X),
      ∃! t : F.obj.obj (op W), ∀ {W' : Grothendieck (slices K)} (θ : W' ⟶ W)
        (hθ : R ((totalForget K).map θ ≫ φ)),
        F.obj.map θ.op t = (xx ((totalForget K).map θ ≫ φ) hθ).1 W' (𝟙 _) := by
    intro W φ
    refine F.property.isSheafFor _ (hcov W φ)
      (fun {W'} θ hθ => (xx ((totalForget K).map θ ≫ φ) hθ).1 W' (𝟙 _)) ?_
    refine (Presieve.compatible_iff_sieveCompatible _).2 ?_
    intro W' W'' θ ρ hθ
    have h2 : R ((totalForget K).map ρ ≫ ((totalForget K).map θ ≫ φ)) :=
      R.downward_closed hθ ((totalForget K).map ρ)
    have e1 := totalForget_map_comp_comp K ρ θ φ
    have h1 : R ((totalForget K).map (ρ ≫ θ) ≫ φ) := by rwa [e1]
    refine Eq.trans (hev (hxc h1 h2 e1)) ?_
    refine Eq.trans (hev (hxs ((totalForget K).map θ ≫ φ) ((totalForget K).map ρ) hθ)) ?_
    refine Eq.trans (ranPresheaf_map_apply J K F ((totalForget K).map ρ).op _ W'' (𝟙 _)) ?_
    refine Eq.trans (congrArg ((xx ((totalForget K).map θ ≫ φ) hθ).1 W'')
      ((Category.id_comp ((totalForget K).map ρ)).trans
        (Category.comp_id ((totalForget K).map ρ)).symm)) ?_
    exact ((xx ((totalForget K).map θ ≫ φ) hθ).2 ρ (𝟙 _)).symm
  choose amal hamal huniq using main
  have hsub : ∀ {W W' : Grothendieck (slices K)} (θ : W' ⟶ W)
      (φ : (totalForget K).obj W ⟶ X),
      F.obj.map θ.op (amal W φ) = amal W' ((totalForget K).map θ ≫ φ) := by
    intro W W' θ φ
    refine huniq W' ((totalForget K).map θ ≫ φ) _ ?_
    intro W'' ρ hρ
    have e1 := totalForget_map_comp_comp K ρ θ φ
    have h1 : R ((totalForget K).map (ρ ≫ θ) ≫ φ) := by rwa [e1]
    refine Eq.trans (map_comp_apply J K F ρ θ (amal W φ)).symm ?_
    refine (hamal W φ (ρ ≫ θ) h1).trans ?_
    exact hev (hxc h1 hρ e1)
  refine ⟨⟨fun W φ => amal W φ, hsub⟩, ?_, ?_⟩
  · intro X' f hf
    refine ranSection_ext J K F fun W φ => (huniq W (φ ≫ f) _ ?_).symm
    intro W' θ hθ
    have e1 : ((totalForget K).map θ ≫ φ) ≫ f = (totalForget K).map θ ≫ (φ ≫ f) :=
      Category.assoc _ _ _
    exact ((xx f hf).2 θ φ).trans ((hres _ _).trans
      ((hev (hxs f _ hf).symm).trans (hev (hxc _ hθ e1))))
  · intro t ht
    refine ranSection_ext J K F fun W φ => (huniq W φ _ ?_)
    intro W' θ hθ
    exact (t.2 θ φ).trans ((hres t _).trans (hev (ht _ hθ)))

/-! ### The comparison morphism -/

/-- The comparison morphism from the restriction of the Kan extension back to `F`: evaluation of
a section of the Kan extension over `j_total(W)` at the identity chart of `W`. -/
def ranEv : (totalForget K).op ⋙ ranPresheaf J K F ⟶ F.obj where
  app W := ↾fun s => s.1 W.unop (𝟙 _)
  naturality {_ W'} θ := ConcreteCategory.hom_ext _ _ fun s =>
    (congrArg (s.1 W'.unop) ((Category.id_comp ((totalForget K).map θ.unop)).trans
      (Category.comp_id ((totalForget K).map θ.unop)).symm)).trans
      (s.2 θ.unop (𝟙 _)).symm

/-- The comparison morphism evaluates a section at the identity chart. -/
theorem ranEv_app_apply (W : (Grothendieck (slices K))ᵒᵖ)
    (s : ((totalForget K).op ⋙ ranPresheaf J K F).obj W) :
    (ranEv J K F).app W s = s.1 W.unop (𝟙 _) :=
  rfl


/-! ### Separatedness along the fibrewise restrictions -/

section Rigid

variable {J K F}

/-- Restriction along an arrow of the total site which `F` inverts is injective on sections. -/
theorem injective_map_of_isIso {W U : Grothendieck (slices K)} (π : W ⟶ U)
    (h : IsIso (F.obj.map π.op)) : Function.Injective (F.obj.map π.op) :=
  ((isIso_iff_bijective _).1 h).1

/-- Restriction along the canonical arrow attached to an equality of objects of the total site
is injective on sections. -/
theorem injective_map_eqToHom {T T' : Grothendieck (slices K)} (e : T = T') :
    Function.Injective (F.obj.map (eqToHom e).op) :=
  have h : IsIso ((eqToHom e).op) := ((eqToIso e).op).isIso_hom
  injective_map_of_isIso (eqToHom e) (@Functor.map_isIso _ _ _ _ _ _ F.obj ((eqToHom e).op) h)

/-- The sieve of arrows of `C` along whose fibrewise restriction two sections of `F` over an
object of the total site agree. -/
def vertSieve {T : Grothendieck (slices K)} (x y : F.obj.obj (op T)) :
    Sieve ((totalForget K).obj T) where
  arrows _ g := F.obj.map (totalVert K T g).op x = F.obj.map (totalVert K T g).op y
  downward_closed := by
    intro A' A'' g hg k
    have h1 : F.obj.map (totalVert K (totalRestrict K T g) k).op
          (F.obj.map (totalVert K T g).op x) =
        F.obj.map (totalVert K (totalRestrict K T g) k).op
          (F.obj.map (totalVert K T g).op y) :=
      congrArg (F.obj.map (totalVert K (totalRestrict K T g) k).op) hg
    have h2 : F.obj.map (eqToHom (totalRestrict_totalRestrict K T g k)).op
          (F.obj.map (totalVert K T (k ≫ g)).op x) =
        F.obj.map (eqToHom (totalRestrict_totalRestrict K T g k)).op
          (F.obj.map (totalVert K T (k ≫ g)).op y) := by
      refine Eq.trans (map_comp_apply J K F _ _ x).symm (Eq.trans ?_ (map_comp_apply J K F _ _ y))
      refine Eq.trans (congrArg (fun z => F.obj.map z.op x) (totalVert_comp K T g k).symm) ?_
      refine Eq.trans ?_ (congrArg (fun z => F.obj.map z.op y) (totalVert_comp K T g k))
      exact (map_comp_apply J K F _ _ x).trans (h1.trans (map_comp_apply J K F _ _ y).symm)
    exact injective_map_eqToHom (totalRestrict_totalRestrict K T g k) h2

/-- An arrow of the total site along which two sections of `F` agree contributes its image in `C`
to the vertical sieve. -/
theorem vertSieve_map (hvert : ∀ {W U : Grothendieck (slices K)} (π : W ⟶ U),
      IsIso ((totalForget K).map π) → IsIso (F.obj.map π.op))
    {T : Grothendieck (slices K)} {x y : F.obj.obj (op T)}
    {W : Grothendieck (slices K)} (θ : W ⟶ T) (h : F.obj.map θ.op x = F.obj.map θ.op y) :
    vertSieve x y ((totalForget K).map θ) := by
  obtain ⟨ρ, hρ, hfac⟩ := exists_factor K θ
  have : IsIso ((totalForget K).map ρ) := hρ ▸ IsIso.id _
  refine injective_map_of_isIso ρ (hvert ρ inferInstance) ?_
  rw [← map_comp_apply J K F ρ, ← map_comp_apply J K F ρ, hfac]
  exact h

/-- **Separatedness along the fibrewise restrictions.** Two sections of `F` over an object of the
total site are equal as soon as their fibrewise restrictions agree along a covering sieve of the
underlying object of `C`. -/
theorem eq_of_vertSieve_mem (_hvert : ∀ {W U : Grothendieck (slices K)} (π : W ⟶ U),
      IsIso ((totalForget K).map π) → IsIso (F.obj.map π.op))
    {T : Grothendieck (slices K)} {x y : F.obj.obj (op T)}
    (h : vertSieve x y ∈ J ((totalForget K).obj T)) : x = y := by
  have hcov := functorPullback_mem_totalTopology K J T (vertSieve x y) h
  obtain ⟨t, -, huniq⟩ := F.property.isSheafFor _ hcov
    (fun {W'} (θ : W' ⟶ T) (_ : (Sieve.functorPullback (totalForget K)
      (vertSieve (F := F) x y)).arrows θ) => F.obj.map θ.op x)
    ((Presieve.compatible_iff_sieveCompatible _).2
      fun W' W'' θ ρ _ => map_comp_apply J K F ρ θ x)
  refine (huniq x fun {W'} θ _ => rfl).trans (huniq y fun {W'} θ hθ => ?_).symm
  obtain ⟨ρ, hρ, hfac⟩ := exists_factor K θ
  refine (congrArg (fun z => F.obj.map z.op y) hfac.symm).trans ?_
  refine (map_comp_apply J K F ρ _ y).trans ((congrArg (F.obj.map ρ.op) hθ.symm).trans ?_)
  exact (map_comp_apply J K F ρ _ x).symm.trans (congrArg (fun z => F.obj.map z.op x) hfac)

end Rigid


/-! ### Local values -/

section LocalValue

variable {J K F}

/-- Restriction along an identity is the identity, on an element. -/
theorem map_id_apply (T : Grothendieck (slices K)) (x : F.obj.obj (op T)) :
    F.obj.map (𝟙 T).op x = x :=
  ConcreteCategory.congr_hom (F.obj.map_id (op T)) x

/-- A *local value* of a section `σ` of `F` over `W₀` at a chart `φ`: a section of `F` over `W`
which restricts to `σ` along every pair of arrows of the total site lying over `φ`. -/
def IsLocalValue {W₀ : Grothendieck (slices K)} (σ : F.obj.obj (op W₀))
    (W : Grothendieck (slices K)) (φ : (totalForget K).obj W ⟶ (totalForget K).obj W₀)
    (t : F.obj.obj (op W)) : Prop :=
  ∀ {M : Grothendieck (slices K)} (a : M ⟶ W) (b : M ⟶ W₀),
    (totalForget K).map b = (totalForget K).map a ≫ φ →
      F.obj.map a.op t = F.obj.map b.op σ

/-- A local value may be read at an equal chart. -/
theorem IsLocalValue.congr_chart {W₀ W : Grothendieck (slices K)} {σ : F.obj.obj (op W₀)}
    {φ φ' : (totalForget K).obj W ⟶ (totalForget K).obj W₀} (h : φ = φ')
    {t : F.obj.obj (op W)} (ht : IsLocalValue σ W φ t) : IsLocalValue σ W φ' t := h ▸ ht

/-- Restricting a local value along an arrow of the total site gives a local value. -/
theorem IsLocalValue.restrict {W₀ W : Grothendieck (slices K)} {σ : F.obj.obj (op W₀)}
    {φ : (totalForget K).obj W ⟶ (totalForget K).obj W₀} {t : F.obj.obj (op W)}
    (ht : IsLocalValue σ W φ t) {W' : Grothendieck (slices K)} (θ : W' ⟶ W) :
    IsLocalValue σ W' ((totalForget K).map θ ≫ φ) (F.obj.map θ.op t) := by
  intro M a b hab
  refine Eq.trans (map_comp_apply J K F a θ t).symm (ht (a ≫ θ) b ?_)
  exact hab.trans (totalForget_map_comp_comp K a θ φ).symm

/-- **A local value is unique.** -/
theorem isLocalValue_unique (hlf : (totalForget K).IsLocallyFull J)
    (hvert : ∀ {W U : Grothendieck (slices K)} (π : W ⟶ U),
      IsIso ((totalForget K).map π) → IsIso (F.obj.map π.op))
    {W₀ W : Grothendieck (slices K)} {σ : F.obj.obj (op W₀)}
    {φ : (totalForget K).obj W ⟶ (totalForget K).obj W₀} {t t' : F.obj.obj (op W)}
    (ht : IsLocalValue σ W φ t) (ht' : IsLocalValue σ W φ t') : t = t' := by
  refine eq_of_vertSieve_mem hvert
    (J.superset_covering ?_ (hlf.functorPushforward_imageSieve_mem φ))
  rintro A g ⟨M, l, κ, ⟨b, hb⟩, rfl⟩
  exact (vertSieve t t').downward_closed
    (vertSieve_map hvert l ((ht l b hb).trans (ht' l b hb).symm)) κ

/-- **A lift of the chart produces a local value.** -/
theorem isLocalValue_of_lift (hlf : (totalForget K).IsLocallyFull J)
    (hrig : ∀ {W U : Grothendieck (slices K)} (ψ ψ' : W ⟶ U),
      (totalForget K).map ψ = (totalForget K).map ψ' → F.obj.map ψ.op = F.obj.map ψ'.op)
    (hvert : ∀ {W U : Grothendieck (slices K)} (π : W ⟶ U),
      IsIso ((totalForget K).map π) → IsIso (F.obj.map π.op))
    {W₀ W N : Grothendieck (slices K)} (σ : F.obj.obj (op W₀))
    (φ : (totalForget K).obj W ⟶ (totalForget K).obj W₀) (π : N ⟶ W)
    (hπ : IsIso ((totalForget K).map π)) (hh : N ⟶ W₀)
    (hhe : (totalForget K).map hh = (totalForget K).map π ≫ φ) :
    ∃ t, IsLocalValue σ W φ t := by
  have := hπ
  obtain ⟨t, hts⟩ := ((isIso_iff_bijective _).1 (hvert π hπ)).2 (F.obj.map hh.op σ)
  refine ⟨t, ?_⟩
  intro M a b hab
  refine eq_of_vertSieve_mem hvert (J.superset_covering ?_
    (hlf.functorPushforward_imageSieve_mem
      ((totalForget K).map a ≫ inv ((totalForget K).map π))))
  rintro A g ⟨Q, c, κ, ⟨d, hd⟩, rfl⟩
  refine (vertSieve _ _).downward_closed (vertSieve_map hvert c ?_) κ
  have e1 : (totalForget K).map (c ≫ a) = (totalForget K).map (d ≫ π) := by
    rw [Functor.map_comp, Functor.map_comp, hd]
    simp
  have e2 : (totalForget K).map (d ≫ hh) = (totalForget K).map (c ≫ b) := by
    rw [Functor.map_comp, Functor.map_comp, hd, hhe, hab]
    simp
  have key : ∀ {P A B Y : Grothendieck (slices K)} (c : P ⟶ A) (a : A ⟶ Y) (d : P ⟶ B)
      (π : B ⟶ Y) (x : F.obj.obj (op Y)),
      (totalForget K).map (c ≫ a) = (totalForget K).map (d ≫ π) →
      F.obj.map c.op (F.obj.map a.op x) = F.obj.map d.op (F.obj.map π.op x) := fun c a d π x e =>
    (map_comp_apply J K F c a x).symm.trans
      ((ConcreteCategory.congr_hom (hrig _ _ e) x).trans (map_comp_apply J K F d π x))
  exact (key c a d π t e1).trans ((congrArg (F.obj.map d.op) hts).trans (key d hh c b σ e2))

/-- Local values transport along an equality of the arrow restricted along. -/
theorem exists_isLocalValue_congr {W₀ W : Grothendieck (slices K)} (σ : F.obj.obj (op W₀))
    (φ : (totalForget K).obj W ⟶ (totalForget K).obj W₀) {A : C}
    {g g' : A ⟶ (totalForget K).obj W} (h : g = g')
    (hex : ∃ t, IsLocalValue σ (totalRestrict K W g) (g ≫ φ) t) :
    ∃ t, IsLocalValue σ (totalRestrict K W g') (g' ≫ φ) t := by
  subst h
  exact hex

end LocalValue


/-! ### Locality and existence of local values -/

section LocalValueExists

variable {J K F}

/-- **Locality of local values**: a local value exists as soon as it exists after a covering of
the underlying object of `C`. -/
theorem isLocalValue_of_cover (hlf : (totalForget K).IsLocallyFull J)
    (hvert : ∀ {W U : Grothendieck (slices K)} (π : W ⟶ U),
      IsIso ((totalForget K).map π) → IsIso (F.obj.map π.op))
    {W₀ W : Grothendieck (slices K)} (σ : F.obj.obj (op W₀))
    (φ : (totalForget K).obj W ⟶ (totalForget K).obj W₀)
    (S : Sieve ((totalForget K).obj W)) (hS : S ∈ J ((totalForget K).obj W))
    (hloc : ∀ ⦃A : C⦄ (g : A ⟶ (totalForget K).obj W), S g →
      ∃ t, IsLocalValue σ (totalRestrict K W g) (g ≫ φ) t) :
    ∃ t, IsLocalValue σ W φ t := by
  have hval : ∀ (W' : Grothendieck (slices K)) (θ : W' ⟶ W), S ((totalForget K).map θ) →
      ∃ t, IsLocalValue σ W' ((totalForget K).map θ ≫ φ) t := by
    intro W' θ hθ
    obtain ⟨tg, htg⟩ := hloc ((totalForget K).map θ) hθ
    obtain ⟨ρ, hρ, hfac⟩ := exists_factor K θ
    refine ⟨F.obj.map ρ.op tg, IsLocalValue.congr_chart ?_ (IsLocalValue.restrict htg ρ)⟩
    exact (congrArg (fun z => z ≫ ((totalForget K).map θ ≫ φ)) hρ).trans (Category.id_comp _)
  choose val hvalspec using hval
  have hcov := functorPullback_mem_totalTopology K J W S hS
  obtain ⟨t, hamal, -⟩ := F.property.isSheafFor _ hcov
    (fun {W'} (θ : W' ⟶ W) (hθ : (Sieve.functorPullback (totalForget K) S).arrows θ) =>
      val W' θ hθ)
    ((Presieve.compatible_iff_sieveCompatible _).2 fun W' W'' θ ρ hθ => by
      refine isLocalValue_unique hlf hvert (hvalspec W'' (ρ ≫ θ) _) ?_
      exact IsLocalValue.congr_chart (totalForget_map_comp_comp K ρ θ φ).symm
        (IsLocalValue.restrict (hvalspec W' θ hθ) ρ))
  refine ⟨t, ?_⟩
  intro M a b hab
  refine eq_of_vertSieve_mem hvert
    (J.superset_covering ?_ (J.pullback_stable ((totalForget K).map a) hS))
  intro A g hg
  have hva : S ((totalForget K).map (totalVert K M g ≫ a)) := by
    rw [Functor.map_comp, totalForget_map_totalVert]
    exact hg
  have hkey := hvalspec (totalRestrict K M g) (totalVert K M g ≫ a) hva
    (𝟙 (totalRestrict K M g)) (totalVert K M g ≫ b) ?_
  · show F.obj.map (totalVert K M g).op (F.obj.map a.op t) =
        F.obj.map (totalVert K M g).op (F.obj.map b.op σ)
    refine Eq.trans (map_comp_apply J K F (totalVert K M g) a t).symm ?_
    refine Eq.trans (hamal (totalVert K M g ≫ a) hva) ?_
    refine Eq.trans (map_id_apply (totalRestrict K M g) _).symm ?_
    exact hkey.trans (map_comp_apply J K F (totalVert K M g) b σ)
  · rw [Functor.map_id, Category.id_comp, Functor.map_comp, Functor.map_comp,
      totalForget_map_totalVert, hab]
    exact (Category.assoc _ _ _).symm

/-- **A local value exists at every chart.** -/
theorem exists_isLocalValue (hlf : (totalForget K).IsLocallyFull J)
    (hrig : ∀ {W U : Grothendieck (slices K)} (ψ ψ' : W ⟶ U),
      (totalForget K).map ψ = (totalForget K).map ψ' → F.obj.map ψ.op = F.obj.map ψ'.op)
    (hvert : ∀ {W U : Grothendieck (slices K)} (π : W ⟶ U),
      IsIso ((totalForget K).map π) → IsIso (F.obj.map π.op))
    {W₀ : Grothendieck (slices K)} (σ : F.obj.obj (op W₀)) (W : Grothendieck (slices K))
    (φ : (totalForget K).obj W ⟶ (totalForget K).obj W₀) :
    ∃ t, IsLocalValue σ W φ t := by
  refine isLocalValue_of_cover hlf hvert σ φ _ (hlf.functorPushforward_imageSieve_mem φ) ?_
  rintro A g ⟨M, l, κ, ⟨b, hb⟩, rfl⟩
  have hge : (totalForget K).map (totalVert K M κ ≫ l) = κ ≫ (totalForget K).map l :=
    ((totalForget K).map_comp (totalVert K M κ) l).trans
      (congrArg (fun z => z ≫ (totalForget K).map l) (totalForget_map_totalVert K M κ))
  refine exists_isLocalValue_congr σ φ hge ?_
  obtain ⟨ρ, hρ, hfac⟩ := exists_factor K (totalVert K M κ ≫ l)
  refine isLocalValue_of_lift hlf hrig hvert σ _ ρ (hρ ▸ IsIso.id _)
    (totalVert K M κ ≫ b) ?_
  refine Eq.trans ?_ (congrArg
    (fun z => z ≫ ((totalForget K).map (totalVert K M κ ≫ l) ≫ φ)) hρ).symm
  refine Eq.trans ?_ (Category.id_comp _).symm
  rw [Functor.map_comp, Functor.map_comp, totalForget_map_totalVert, hb]
  exact (Category.assoc _ _ _).symm

end LocalValueExists


/-! ### The comparison morphism is an isomorphism -/

section EssImage

variable {J K F}

/-- **The comparison morphism is bijective on sections**, for a rigid sheaf. -/
theorem ranEv_app_bijective (hlf : (totalForget K).IsLocallyFull J)
    (hrig : ∀ {W U : Grothendieck (slices K)} (ψ ψ' : W ⟶ U),
      (totalForget K).map ψ = (totalForget K).map ψ' → F.obj.map ψ.op = F.obj.map ψ'.op)
    (hvert : ∀ {W U : Grothendieck (slices K)} (π : W ⟶ U),
      IsIso ((totalForget K).map π) → IsIso (F.obj.map π.op))
    (W₀ : Grothendieck (slices K)) :
    Function.Bijective ((ranEv J K F).app (op W₀)) := by
  constructor
  · intro s s' hss
    refine ranSection_ext J K F fun W φ => ?_
    have hloc : ∀ s : ranSection J K F ((totalForget K).obj W₀),
        IsLocalValue (s.1 W₀ (𝟙 _)) W (φ : (totalForget K).obj W ⟶ (totalForget K).obj W₀)
          (s.1 W φ) := fun s M a b hab =>
      ((s.2 a φ).trans (congrArg (s.1 M) (hab.symm.trans (Category.comp_id _).symm))).trans
        (s.2 b (𝟙 _)).symm
    refine isLocalValue_unique hlf hvert (hloc s) ?_
    rw [show s.1 W₀ (𝟙 _) = s'.1 W₀ (𝟙 _) from hss]
    exact hloc s'
  · intro σ
    choose val hval using exists_isLocalValue hlf hrig hvert σ
    refine ⟨⟨fun W φ => val W φ, fun {W W'} θ φ => ?_⟩, ?_⟩
    · exact isLocalValue_unique hlf hvert
        (IsLocalValue.restrict (hval W φ) θ) (hval W' ((totalForget K).map θ ≫ φ))
    · refine isLocalValue_unique hlf hvert (hval W₀ (𝟙 _)) ?_
      intro M a b hab
      exact ConcreteCategory.congr_hom (hrig a b (hab.trans (Category.comp_id _)).symm) σ

/-- **A rigid sheaf on the total site is an inverse image along `j_total`.** -/
theorem essImage_of_rigid (hlf : (totalForget K).IsLocallyFull J)
    (hrig : ∀ {W U : Grothendieck (slices K)} (ψ ψ' : W ⟶ U),
      (totalForget K).map ψ = (totalForget K).map ψ' → F.obj.map ψ.op = F.obj.map ψ'.op)
    (hvert : ∀ {W U : Grothendieck (slices K)} (π : W ⟶ U),
      IsIso ((totalForget K).map π) → IsIso (F.obj.map π.op)) :
    (totalLocalizationMorphism J K).inverseImage.essImage F := by
  have happ : ∀ W, IsIso ((ranEv J K F).app W) := fun W =>
    (isIso_iff_bijective _).2 (ranEv_app_bijective hlf hrig hvert W.unop)
  refine ⟨⟨ranPresheaf J K F, isSheaf_ranPresheaf J K F⟩, ⟨?_⟩⟩
  refine (fullyFaithfulSheafToPresheaf ((situation J K).totalTopology) (Type u)).preimageIso ?_
  exact NatIso.ofComponents (fun W => @asIso _ _ _ _ ((ranEv J K F).app W) (happ W))
    fun θ => (ranEv J K F).naturality θ

end EssImage

/-! ### Stacks 0D8E: essential surjectivity onto the cartesian sheaves -/

section Hypercovering

variable [HasEqualizers C] [HasPullbacks C]

/-- **Essential surjectivity of `a⁻¹` onto the cartesian sheaves of sets.** For a hypercovering
`K` of the final presheaf, every cartesian sheaf of sets on the total site `(C/K)_total` lies in
the essential image of restriction along the localization functor `j_total`. -/
theorem essImage_of_isCartesianSheaf (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P)
    (E : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology (Type u))
    (hE : (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf E) :
    (totalLocalizationMorphism P.toGrothendieck
      H.toSimplicialObject).inverseImage.essImage E :=
  essImage_of_rigid (isLocallyFull_totalForget P H)
    (fun ψ ψ' h => map_eq_of_totalForget_map_eq P H E hE ψ ψ' h)
    (fun π h => isIso_map_of_isIso_totalForget_map P.toGrothendieck H.toSimplicialObject E hE π h)

/-- **Stacks 0D8E (1), the essential image is exactly the cartesian sheaves of sets.** A sheaf of
sets on the total site of a hypercovering of the final presheaf lies in the essential image of
restriction along the localization functor `j_total` if and only if it is cartesian. -/
@[stacks 0D8E "part (1): essential image = cartesian sheaves of sets"]
theorem mem_essImage_iff_isCartesianSheaf' (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P)
    (E : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology (Type u)) :
    (totalLocalizationMorphism P.toGrothendieck
        H.toSimplicialObject).inverseImage.essImage E ↔
      (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf E :=
  ⟨isCartesianSheaf_of_mem_essImage P.toGrothendieck H.toSimplicialObject,
    essImage_of_isCartesianSheaf P H E⟩

/-- **Stacks 0D8E (1), `a⁻¹ a_* F = F` for cartesian `F`.** For a cartesian sheaf of sets `E` on
the total site of a hypercovering of the final presheaf, the counit `a⁻¹ a_* E ⟶ E` is an
isomorphism. -/
@[stacks 0D8E "part (1): a^{-1} a_* F = F for cartesian F"]
theorem isIso_counit_app_hypercovering' (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P)
    (E : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology (Type u))
    (hE : (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf E) :
    IsIso ((totalLocalizationMorphism P.toGrothendieck
      H.toSimplicialObject).adj.counit.app E) :=
  (isIso_counit_app_iff_mem_essImage_of_isLocallyFull P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) (isLocallyFull_totalForget P H) E).mpr
    (essImage_of_isCartesianSheaf P H E hE)

end Hypercovering

end CategoryTheory.SimplicialSemiRepresentable

end
