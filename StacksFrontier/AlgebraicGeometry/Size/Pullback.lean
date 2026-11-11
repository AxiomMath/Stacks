module

import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Localization.Cardinality
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier


/-!
# Size of a fibre product of schemes (Stacks 04T6)

The *size* of a scheme (`AlgebraicGeometry.Scheme.size`, Stacks Section 000H) is the maximum of `ℵ₀`,
the number of its affine opens, and the cardinalities of its rings of sections over affine
opens. This file shows that size does not grow under fibre products:
`size (X ×_S Y) ≤ max (size X) (size Y)`.

The formalization follows the source argument. Affine opens `Spec R ⊆ S`, `Spec A ⊆ X` and
`Spec B ⊆ Y` with `Spec A` and `Spec B` lying over `Spec R` cut out an affine open
`Spec A ×_{Spec R} Spec B ≅ Spec (A ⊗_R B)` of `X ×_S Y` (`pullbackSpecIso`), and these opens
cover the fibre product. Writing `κ := max (size X) (size Y)`, the cover is indexed by
quadruples consisting of two affine opens and two sections over them, so its index type has
cardinality `≤ κ`, and each cover ring `A ⊗_R B` is a quotient of the free module on `A × B`,
so it too has cardinality `≤ κ`.

The two halves of `size` are then bounded separately. The basic opens `D(c)`, `c ∈ A ⊗_R B`,
inside the cover pieces form a Zariski basis `ℬ` of cardinality `≤ κ`; an affine open of the
fibre product is quasi-compact, hence a finite union of basis opens, and the map sending it to
that finite set of basis opens is injective, which bounds the number of affine opens by
`#(Finset ℬ) ≤ κ`. For the sections over an affine open `W`, the sheaf separation axiom
injects `Γ(W)` into a finite product of sections over basic opens, each a localization of a
cover ring and hence of cardinality `≤ κ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal TopologicalSpace

universe u

namespace Cardinal

/-- The cardinality of a tensor product of `R`-modules in a single universe is at most
`max ℵ₀ (max #M #N)`: every element is a finite sum of pure tensors, so summing the pure
tensors of a list gives a surjection `List (M × N) → M ⊗[R] N`. -/
lemma mk_tensorProduct_le {R : Type u} [CommSemiring R] {M : Type u} [AddCommMonoid M] [Module R M]
    {N : Type u} [AddCommMonoid N] [Module R N] :
    #(TensorProduct R M N) ≤ max ℵ₀ (max #M #N) := by
  have hsurj : Function.Surjective
      fun l : List (M × N) => (l.map fun (m, n) => m ⊗ₜ[R] n).sum := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul m n => exact ⟨[(m, n)], by simp⟩
    | add x y hx hy =>
      obtain ⟨lx, rfl⟩ := hx
      obtain ⟨ly, rfl⟩ := hy
      exact ⟨lx ++ ly, by simp⟩
  calc #(TensorProduct R M N) ≤ #(List (M × N)) := mk_le_of_surjective hsurj
    _ ≤ max ℵ₀ #(M × N) := mk_list_le_max _
    _ ≤ max ℵ₀ (max #M #N) := by
      rw [mk_prod, lift_id, lift_id]
      exact max_le (le_max_left _ _)
        ((mul_le_max _ _).trans (max_le (le_max_right _ _) (le_max_left _ _)))

/-- A sum of at most `κ` cardinals, each at most an infinite cardinal `κ`, is at most `κ`. -/
lemma sum_le_of_mk_le_of_forall_le {J : Type u} {c : J → Cardinal.{u}} {κ : Cardinal.{u}}
    (hκ0 : ℵ₀ ≤ κ) (hJ : #J ≤ κ) (hc : ∀ j, c j ≤ κ) : Cardinal.sum c ≤ κ :=
  ((sum_le_sum _ _ hc).trans_eq (sum_const' J κ)).trans
    ((mul_le_mul' hJ le_rfl).trans_eq (mul_eq_self hκ0))

end Cardinal

namespace AlgebraicGeometry

/-- The global sections of a fibre product of affine schemes `A ×_{Sc} B` have cardinality at
most any infinite cardinal `κ` bounding the section rings of the two factors: the fibre product
is `Spec (Γ(A) ⊗_{Γ(Sc)} Γ(B))`, whose cardinality `Cardinal.mk_tensorProduct_le` bounds. -/
private lemma Scheme.mk_sections_top_pullback_le {A B Sc : Scheme.{u}} [IsAffine A] [IsAffine B]
    [IsAffine Sc] (f' : A ⟶ Sc) (g' : B ⟶ Sc) (κ : Cardinal.{u}) (hκ0 : ℵ₀ ≤ κ)
    (hA : #Γ(A, ⊤) ≤ κ) (hB : #Γ(B, ⊤) ≤ κ) : #Γ(pullback f' g', ⊤) ≤ κ := by
  have hspec : IsPullback
      (pullback.fst f' g' ≫ A.isoSpec.hom) (pullback.snd f' g' ≫ B.isoSpec.hom)
      (Spec.map f'.appTop) (Spec.map g'.appTop) :=
    (IsPullback.of_hasPullback f' g').of_iso (Iso.refl _) A.isoSpec B.isoSpec Sc.isoSpec
      (by simp) (by simp) (Scheme.isoSpec_hom_naturality f').symm
      (Scheme.isoSpec_hom_naturality g').symm
  let : Algebra Γ(Sc, ⊤) Γ(A, ⊤) := f'.appTop.hom.toAlgebra
  let : Algebra Γ(Sc, ⊤) Γ(B, ⊤) := g'.appTop.hom.toAlgebra
  have hfmap : CommRingCat.ofHom (algebraMap Γ(Sc, ⊤) Γ(A, ⊤)) = f'.appTop := by
    ext x
    rfl
  have hgmap : CommRingCat.ofHom (algebraMap Γ(Sc, ⊤) Γ(B, ⊤)) = g'.appTop := by
    ext x
    rfl
  let TT := TensorProduct (Γ(Sc, ⊤) : CommRingCat).carrier
      (Γ(A, ⊤) : CommRingCat).carrier (Γ(B, ⊤) : CommRingCat).carrier
  have iso2 : pullback (Spec.map f'.appTop) (Spec.map g'.appTop) ≅ Spec (CommRingCat.of TT) :=
    hfmap ▸ hgmap ▸ pullbackSpecIso Γ(Sc, ⊤) Γ(A, ⊤) Γ(B, ⊤)
  set φ := hspec.isoIsPullback _ _
    (IsPullback.of_hasPullback (Spec.map f'.appTop) (Spec.map g'.appTop)) ≪≫ iso2
  have isoΓ : Γ(pullback f' g', ⊤) ≅ CommRingCat.of TT :=
    (Scheme.Γ.mapIso φ.op).symm ≪≫ Scheme.ΓSpecIso _
  exact (mk_congr isoΓ.commRingCatIsoToRingEquiv.toEquiv).trans_le
    (mk_tensorProduct_le.trans (max_le hκ0 (max_le hA hB)))

/-- An open `U ⊆ X` whose `f`-image lies in an open `S₀ ⊆ S` has `Set.range (U.ι ≫ f).base`
contained in the range of `S₀.ι`, so that `U.ι ≫ f` factors through `S₀`. -/
lemma range_comp_ι_subset_range_ι {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} {S₀ : S.Opens}
    (hU : U ≤ f ⁻¹ᵁ S₀) : Set.range (U.ι ≫ f).base ⊆ Set.range S₀.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro x ⟨y, rfl⟩
  simpa [Scheme.Hom.comp_base] using hU (show (U.ι.base y : X) ∈ U from y.2)

/-- For opens `U ⊆ X` and `V ⊆ Y` lying over an open `S₀ ⊆ S`, the fibre product of `U` and `V`
over `S` is also a fibre product of `U` and `V` over `S₀`, because `S₀.ι` is a monomorphism. -/
lemma exists_isoPullback_of_le_preimage {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {U : X.Opens} {V : Y.Opens} {S₀ : S.Opens} (hU : U ≤ f ⁻¹ᵁ S₀) (hV : V ≤ g ⁻¹ᵁ S₀) :
    ∃ (f' : U.toScheme ⟶ S₀.toScheme) (g' : V.toScheme ⟶ S₀.toScheme),
      Nonempty (pullback f' g' ≅ pullback (U.ι ≫ f) (V.ι ≫ g)) := by
  have hlift : ∀ {Z : Scheme.{u}} (h : Z ⟶ S) (hh : Set.range h.base ⊆ Set.range S₀.ι.base),
      ∃ h' : Z ⟶ S₀.toScheme, h' ≫ S₀.ι = h := fun h hh =>
    ⟨IsOpenImmersion.lift S₀.ι h hh, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨f', hf'⟩ := hlift _ (range_comp_ι_subset_range_ι f hU)
  obtain ⟨g', hg'⟩ := hlift _ (range_comp_ι_subset_range_ι g hV)
  have hpb : IsPullback (pullback.fst f' g') (pullback.snd f' g') (f' ≫ S₀.ι) (g' ≫ S₀.ι) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono f' g' S₀.ι)
  rw [hf', hg'] at hpb
  exact ⟨f', g', ⟨hpb.isoPullback⟩⟩

/-- The canonical open immersion of the fibre product of opens `U ⊆ X` and `V ⊆ Y` into `X ×_S Y`
has image `pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V`. -/
lemma Scheme.Pullback.opensRange_map_ι {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : X.Opens) (V : Y.Opens) :
    (pullback.map (U.ι ≫ f) (V.ι ≫ g) f g U.ι V.ι (𝟙 S) (by simp) (by simp)).opensRange
      = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
  refine Opens.ext ?_
  rw [Scheme.Hom.coe_opensRange,
    Scheme.Pullback.range_map (U.ι ≫ f) (V.ι ≫ g) f g U.ι V.ι (𝟙 S) (by simp) (by simp),
    Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  rfl

/-- The sections of `X ×_S Y` over `pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V`, for opens
`U ⊆ X` and `V ⊆ Y`, are the global sections of the fibre product of `U` and `V` over `S`. -/
lemma Scheme.mk_sections_inf_preimage_eq {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : X.Opens) (V : Y.Opens) :
    #Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
      = #Γ(pullback (U.ι ≫ f) (V.ι ≫ g), ⊤) :=
  have hmtop : (pullback.map (U.ι ≫ f) (V.ι ≫ g) f g U.ι V.ι (𝟙 S) (by simp) (by simp)) ''ᵁ ⊤
      = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V :=
    (Opens.ext (by simp [Scheme.Hom.opensRange])).trans (Scheme.Pullback.opensRange_map_ι f g U V)
  mk_congr ((pullback f g).presheaf.mapIso (eqToIso hmtop).op ≪≫
    Scheme.Hom.appIso _ ⊤).commRingCatIsoToRingEquiv.toEquiv

/-- For affine opens `U ⊆ X` and `V ⊆ Y` lying over an affine open `S₀ ⊆ S`, the open
`pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V` of `X ×_S Y` is affine. -/
lemma isAffineOpen_inf_preimage {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {U : X.Opens} {V : Y.Opens} {S₀ : S.Opens}
    [IsAffine U.toScheme] [IsAffine V.toScheme] [IsAffine S₀.toScheme]
    (hU : U ≤ f ⁻¹ᵁ S₀) (hV : V ≤ g ⁻¹ᵁ S₀) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  obtain ⟨f', g', ⟨e⟩⟩ := exists_isoPullback_of_le_preimage f g hU hV
  have : IsAffine (pullback (U.ι ≫ f) (V.ι ≫ g)) :=
    (IsAffine.iff_of_isIso e.hom).mp inferInstance
  rw [← Scheme.Pullback.opensRange_map_ι f g U V]
  exact isAffineOpen_opensRange _

/-- The sections of `X ×_S Y` over `pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V`, for affine
opens `U ⊆ X` and `V ⊆ Y` lying over an affine open `S₀ ⊆ S`, have cardinality at most any
infinite cardinal `κ` bounding `#Γ(X, U)` and `#Γ(Y, V)`. -/
lemma Scheme.mk_sections_inf_preimage_le {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {U : X.Opens} {V : Y.Opens} {S₀ : S.Opens}
    [IsAffine U.toScheme] [IsAffine V.toScheme] [IsAffine S₀.toScheme]
    (hU : U ≤ f ⁻¹ᵁ S₀) (hV : V ≤ g ⁻¹ᵁ S₀) (κ : Cardinal.{u}) (hκ0 : ℵ₀ ≤ κ)
    (hUcard : #Γ(X, U) ≤ κ) (hVcard : #Γ(Y, V) ≤ κ) :
    #Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ≤ κ := by
  obtain ⟨f', g', ⟨e⟩⟩ := exists_isoPullback_of_le_preimage f g hU hV
  rw [Scheme.mk_sections_inf_preimage_eq f g U V]
  refine (mk_congr (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv.toEquiv).trans_le ?_
  exact Scheme.mk_sections_top_pullback_le f' g' κ hκ0
    ((mk_congr U.topIso.commRingCatIsoToRingEquiv.toEquiv).trans_le hUcard)
    ((mk_congr V.topIso.commRingCatIsoToRingEquiv.toEquiv).trans_le hVcard)

/-- Every point of `X ×_S Y` lies in `pullback.fst f g ⁻¹ᵁ D(a) ⊓ pullback.snd f g ⁻¹ᵁ D(b)` for
a basic open `D(a)` of an affine open of `X` and a basic open `D(b)` of an affine open of `Y`,
both lying over one affine open of `S`. -/
lemma exists_basicOpen_mem_inf_preimage {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (x : (pullback f g : Scheme.{u})) :
    ∃ (U : X.affineOpens) (a : Γ(X, U.1)) (V : Y.affineOpens) (b : Γ(Y, V.1))
        (S₀ : S.affineOpens), X.basicOpen a ≤ f ⁻¹ᵁ S₀.1 ∧ Y.basicOpen b ≤ g ⁻¹ᵁ S₀.1 ∧
      (pullback.fst f g).base x ∈ X.basicOpen a ∧ (pullback.snd f g).base x ∈ Y.basicOpen b := by
  have hfg : f.base ((pullback.fst f g).base x) = g.base ((pullback.snd f g).base x) := by
    simpa [Scheme.Hom.comp_base] using
      congrArg (fun n : pullback f g ⟶ S => n.base x) (pullback.condition (f := f) (g := g))
  obtain ⟨S₀, hS₀aff, hfpxS₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := f.base ((pullback.fst f g).base x)) (U := ⊤) (Opens.mem_top _)
  obtain ⟨U, hUaff, hpxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := (pullback.fst f g).base x) (U := ⊤) (Opens.mem_top _)
  obtain ⟨a, haleq, hpxDa⟩ :=
    hUaff.exists_basicOpen_le (V := f ⁻¹ᵁ S₀) ⟨(pullback.fst f g).base x, hfpxS₀⟩ hpxU
  obtain ⟨V, hVaff, hqxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := (pullback.snd f g).base x) (U := ⊤) (Opens.mem_top _)
  have hqxpre : (pullback.snd f g).base x ∈ g ⁻¹ᵁ S₀ :=
    show g.base ((pullback.snd f g).base x) ∈ S₀ from hfg ▸ hfpxS₀
  obtain ⟨b, hbleq, hqxDb⟩ :=
    hVaff.exists_basicOpen_le (V := g ⁻¹ᵁ S₀) ⟨(pullback.snd f g).base x, hqxpre⟩ hqxV
  exact ⟨⟨U, hUaff⟩, a, ⟨V, hVaff⟩, b, ⟨S₀, hS₀aff⟩, haleq, hbleq, hpxDa, hqxDb⟩

/-- The fibre product `X ×_S Y` admits an affine open cover indexed by a type of cardinality
at most `max (size X) (size Y)`, all of whose pieces have section ring of cardinality at most
`max (size X) (size Y)`.

The pieces are the opens `pullback.fst f g ⁻¹ᵁ D(a) ⊓ pullback.snd f g ⁻¹ᵁ D(b)` for basic
affine opens `D(a) ⊆ X` and `D(b) ⊆ Y` lying over a common affine open of `S`. Both halves of
the bound on `size (X ×_S Y)` follow from this single geometric input by cardinal arithmetic
and general topology. -/
private lemma exists_small_affine_cover {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    ∃ (I : Type u) (W : I → (pullback f g).affineOpens),
      (⨆ i, (W i).1) = ⊤ ∧ #I ≤ max (Scheme.size X) (Scheme.size Y) ∧
      ∀ i, #Γ(pullback f g, (W i).1) ≤ max (Scheme.size X) (Scheme.size Y) := by
  set κ := max (Scheme.size X) (Scheme.size Y)
  have hκ0 : ℵ₀ ≤ κ := (Scheme.aleph0_le_size X).trans (le_max_left _ _)
  set P := pullback f g
  set p := pullback.fst f g
  set q := pullback.snd f g
  -- The index type: compatible pairs of basic opens of `X` and `Y` sitting over a common
  -- affine open of `S`.
  set I : Type u :=
    Σ (U : X.affineOpens) (_a : (X.presheaf.obj (Opposite.op U.1) : Type u))
        (V : Y.affineOpens) (_b : (Y.presheaf.obj (Opposite.op V.1) : Type u)),
      PLift (∃ S₀ : S.affineOpens,
        (X.basicOpen _a ≤ f ⁻¹ᵁ S₀.1) ∧ (Y.basicOpen _b ≤ g ⁻¹ᵁ S₀.1)) with hI
  set openOf : I → P.Opens :=
    fun ⟨_, a, _, b, _⟩ => p ⁻¹ᵁ X.basicOpen a ⊓ q ⁻¹ᵁ Y.basicOpen b
  -- Every such open is affine with a small ring of sections; both facts come from the same
  -- affine-pullback computation.
  have key : ∀ i : I, IsAffineOpen (openOf i) ∧ #Γ(P, openOf i) ≤ κ := by
    rintro ⟨⟨U, hU⟩, a, ⟨V, hV⟩, b, ⟨⟨S₀, hS₀⟩, ha, hb⟩⟩
    have hDa : IsAffineOpen (X.basicOpen a) := hU.basicOpen a
    have hDb : IsAffineOpen (Y.basicOpen b) := hV.basicOpen b
    have : IsAffine (X.basicOpen a).toScheme := hDa
    have : IsAffine (Y.basicOpen b).toScheme := hDb
    have : IsAffine S₀.toScheme := hS₀
    exact ⟨isAffineOpen_inf_preimage f g ha hb,
      Scheme.mk_sections_inf_preimage_le f g ha hb κ hκ0
        ((Scheme.mk_sections_le_size X ⟨_, hDa⟩).trans (le_max_left _ _))
        ((Scheme.mk_sections_le_size Y ⟨_, hDb⟩).trans (le_max_right _ _))⟩
  choose hAff hΓ using key
  refine ⟨I, fun i => ⟨openOf i, hAff i⟩, ?_, ?_, hΓ⟩
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨U, a, V, b, S₀, ha, hb, hxa, hxb⟩ := exists_basicOpen_mem_inf_preimage f g x
    exact Opens.mem_iSup.mpr ⟨⟨U, a, V, b, ⟨S₀, ha, hb⟩⟩, hxa, hxb⟩
  · -- `I` is a sigma over `U : X.affineOpens`, `a : Γ(X, U)`, `V : Y.affineOpens`,
    -- `b : Γ(Y, V)`, with a subsingleton `PLift` tail; each base and fibre has cardinality
    -- `≤ κ`, and `κ` infinite makes the iterated sum `≤ κ`.
    rw [hI, mk_sigma]
    refine sum_le_of_mk_le_of_forall_le hκ0
      ((Scheme.mk_affineOpens_le_size X).trans (le_max_left _ _)) fun U => ?_
    rw [mk_sigma]
    refine sum_le_of_mk_le_of_forall_le hκ0
      ((Scheme.mk_sections_le_size X U).trans (le_max_left _ _)) fun a => ?_
    rw [mk_sigma]
    refine sum_le_of_mk_le_of_forall_le hκ0
      ((Scheme.mk_affineOpens_le_size Y).trans (le_max_right _ _)) fun V => ?_
    exact (mk_le_of_injective Sigma.fst_injective).trans
      ((Scheme.mk_sections_le_size Y V).trans (le_max_right _ _))

/-- The basic opens `D(c)`, `c ∈ Γ(P, W i)`, inside the members of an affine open cover `W` of a
scheme `P` form a basis of the topology of `P`. -/
lemma Scheme.isBasis_basicOpen_of_iSup_eq_top {P : Scheme.{u}} {I : Type u}
    (W : I → P.affineOpens) (hW : (⨆ i, (W i).1) = ⊤) :
    Opens.IsBasis (Set.range fun c : Σ i, Γ(P, (W i).1) => P.basicOpen c.2) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hxU
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hW.ge (Opens.mem_top x))
  obtain ⟨a, hale, hxa⟩ := (W i).2.exists_basicOpen_le (V := U ⊓ (W i).1) ⟨x, hxU, hxi⟩ hxi
  exact ⟨P.basicOpen a, ⟨⟨i, a⟩, rfl⟩, hxa, hale.trans inf_le_left⟩

/-- The fibre product `X ×_S Y` has a Zariski basis of cardinality at most
`max (size X) (size Y)`, all of whose members have section ring of cardinality at most
`max (size X) (size Y)`: take the basic opens inside the pieces of a small affine cover. -/
private lemma exists_small_basis {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    ∃ ℬ : Set (pullback f g).Opens, Opens.IsBasis ℬ ∧
      #ℬ ≤ max (Scheme.size X) (Scheme.size Y) ∧
      ∀ B ∈ ℬ, #Γ(pullback f g, B) ≤ max (Scheme.size X) (Scheme.size Y) := by
  obtain ⟨I, W, hWcov, hIcard, hWΓcard⟩ := exists_small_affine_cover f g
  refine ⟨Set.range fun c : Σ i, Γ(pullback f g, (W i).1) => (pullback f g).basicOpen c.2,
    Scheme.isBasis_basicOpen_of_iSup_eq_top W hWcov, ?_, ?_⟩
  · refine mk_range_le.trans ?_
    rw [mk_sigma]
    exact sum_le_of_mk_le_of_forall_le ((Scheme.aleph0_le_size X).trans (le_max_left _ _))
      hIcard hWΓcard
  · rintro B ⟨⟨i, a⟩, rfl⟩
    have := (W i).2.isLocalization_basicOpen a
    exact (IsLocalization.cardinalMk_le (Submonoid.powers a)).trans (hWΓcard i)

/-- A scheme whose topology has a basis `ℬ` of cardinality at most an infinite cardinal `κ` has at
most `κ` affine opens: an affine open is quasi-compact, hence the supremum of a finite subset of
`ℬ`, and that finite subset determines it. -/
lemma Scheme.mk_affineOpens_le_of_isBasis {P : Scheme.{u}} {ℬ : Set P.Opens}
    (hℬbasis : Opens.IsBasis ℬ) {κ : Cardinal.{u}} (hκ0 : ℵ₀ ≤ κ) (hℬcard : #ℬ ≤ κ) :
    #P.affineOpens ≤ κ := by
  choose Us hUsSub hUsFin hUsEq using fun U : P.affineOpens =>
    hℬbasis.exists_finite_of_isCompact U.2.isCompact
  have hpreFin : ∀ U : P.affineOpens, (Subtype.val ⁻¹' (Us U) : Set ℬ).Finite :=
    fun U => Set.Finite.preimage Subtype.val_injective.injOn (hUsFin U)
  refine (mk_le_of_injective (f := fun U => (hpreFin U).toFinset) ?_).trans ?_
  · intro U₁ U₂ h
    -- Equal finsets give equal preimages in `↑ℬ`, and `Us · ⊆ ℬ` recovers `Us U₁ = Us U₂`.
    have hset : (Subtype.val ⁻¹' (Us U₁) : Set ℬ) = Subtype.val ⁻¹' (Us U₂) := by
      simpa [Set.Finite.coe_toFinset] using congrArg (fun s : Finset ℬ => (s : Set ℬ)) h
    have himg : Us U₁ = Us U₂ := by
      have hpre : ∀ U, Subtype.val '' (Subtype.val ⁻¹' (Us U) : Set ℬ) = Us U := fun U => by
        rw [Subtype.image_preimage_coe]
        exact Set.inter_eq_right.mpr (hUsSub U)
      rw [← hpre U₁, ← hpre U₂, hset]
    exact Subtype.ext (by rw [hUsEq U₁, hUsEq U₂, himg])
  · rcases finite_or_infinite ℬ with h | h
    · exact (lt_aleph0_of_finite _).le.trans hκ0
    · exact (mk_finset_of_infinite ℬ).trans_le hℬcard

/-- The number of affine opens of a fibre product is at most `max (size X) (size Y)`: the
basic opens inside a small affine cover form a Zariski basis `ℬ` of cardinality `≤ κ`, and a
quasi-compact open is determined by a finite subset of `ℬ` covering it. -/
theorem Scheme.mk_affineOpens_pullback_le {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    #(pullback f g).affineOpens ≤ max (Scheme.size X) (Scheme.size Y) := by
  obtain ⟨ℬ, hℬbasis, hℬcard, -⟩ := exists_small_basis f g
  exact Scheme.mk_affineOpens_le_of_isBasis hℬbasis
    ((Scheme.aleph0_le_size X).trans (le_max_left _ _)) hℬcard

/-- The sections over an open covered by finitely many opens whose section rings all have
cardinality at most an infinite cardinal `κ` themselves have cardinality at most `κ`: the sheaf
separation axiom injects them into the finite product of the sections over the cover. -/
lemma Scheme.mk_sections_le_of_eq_iSup {P : Scheme.{u}} {W : P.Opens} {ι : Type u}
    [Finite ι] {D : ι → P.Opens} (hDcov : W = ⨆ i, D i) {κ : Cardinal.{u}} (hκ0 : ℵ₀ ≤ κ)
    (hDcard : ∀ i, #Γ(P, D i) ≤ κ) : #Γ(P, W) ≤ κ :=
  have := Fintype.ofFinite ι
  (P.mk_sections_le_prod_of_iSup Finset.univ D W (by simpa using hDcov)).trans
    (prod_le_of_le_of_aleph0_le _ _ κ hκ0 fun i _ => hDcard i)

/-- The sections over an affine open of a fibre product have cardinality at most
`max (size X) (size Y)`: the open is a finite union of basic opens of the affine cover, the
sheaf separation axiom injects its sections into the product of the sections over those, and
each factor is a localization of a cover ring. -/
theorem Scheme.mk_sections_pullback_le {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (W : (pullback f g).affineOpens) :
    #Γ(pullback f g, W.1) ≤ max (Scheme.size X) (Scheme.size Y) := by
  obtain ⟨ℬ, hℬbasis, -, hℬΓ⟩ := exists_small_basis f g
  -- `W` is affine, hence compact, hence a finite union of basis elements.
  obtain ⟨Us, hUsSub, hUsFin, hUsEq⟩ := hℬbasis.exists_finite_of_isCompact W.2.isCompact
  have := hUsFin.to_subtype
  exact Scheme.mk_sections_le_of_eq_iSup (D := Subtype.val)
    (by rw [hUsEq, sSup_eq_iSup']) ((Scheme.aleph0_le_size X).trans (le_max_left _ _))
    fun B => hℬΓ B (hUsSub B.2)

/-- **Stacks 04T6.** The size of a fibre product of schemes is bounded by the maximum of the
sizes of the two factors. -/
@[stacks 04T6]
theorem Scheme.size_pullback_le {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Scheme.size (pullback f g) ≤ max (Scheme.size X) (Scheme.size Y) :=
  max_le ((le_max_left _ _).trans (le_max_left _ _))
    (max_le (Scheme.mk_affineOpens_pullback_le f g)
      (ciSup_le' (Scheme.mk_sections_pullback_le f g)))

end AlgebraicGeometry
