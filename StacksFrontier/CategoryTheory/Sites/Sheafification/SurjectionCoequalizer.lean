module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Sites.Sheafification.InjectiveSurjective

/-!
# A surjection of sheaves of sets is the coequalizer of its kernel pair

A surjection `φ : F ⟶ G` of sheaves of sets on a site — one for which every section of `G` is
locally in the image — exhibits `G` as the coequalizer of the two projections `F ×_G F ⇉ F`.

## Main results

* `Stacks.Sites.SurjectionCoequalizer.coequalizer_of_surjection`: the canonical cofork
  `F ×_G F ⇉ F → G` of a surjection of sheaves of sets is a colimit cofork.

## References

* [Stacks Project, Tag 086K](https://stacks.math.columbia.edu/tag/086K)
-/

@[expose] public section

open CategoryTheory Limits Opposite


universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

namespace Stacks.Sites.SurjectionCoequalizer

/-- The canonical cofork `F ×_G F ⇉ F → G`. -/
noncomputable def coequalizerCofork {F G : Sheaf J (Type max v u)} (φ : F ⟶ G) :
    Cofork (pullback.fst φ φ) (pullback.snd φ φ) :=
  Cofork.ofπ φ pullback.condition

/-- Sections of a sheaf of sets agreeing along a covering sieve are equal. -/
lemma sheaf_separated
    (X : Sheaf J (Type max v u)) {U : C} {S : Sieve U} (hS : S ∈ J U)
    (x y : X.obj.obj (op U))
    (h : ∀ ⦃V : C⦄ (f : V ⟶ U), S f → X.obj.map f.op x = X.obj.map f.op y) :
    x = y :=
  (((isSheaf_iff_isSheaf_of_type J X.obj).mp X.property S hS).isSeparatedFor).ext
    (fun _ f hf => h f hf)

/-- Two sections of `F` with equal images in `G` lift to a section of `F ×_G F`. -/
lemma exists_pullback_section
    {F G : Sheaf J (Type max v u)} (φ : F ⟶ G)
    {V : C} (t₁ t₂ : F.obj.obj (op V))
    (heq : φ.hom.app (op V) t₁ = φ.hom.app (op V) t₂) :
    ∃ p : (pullback φ φ).obj.obj (op V),
      (pullback.fst φ φ).hom.app (op V) p = t₁ ∧
      (pullback.snd φ φ).hom.app (op V) p = t₂ := by
  let H : Sheaf J (Type max v u) ⥤ Type max v u :=
    sheafToPresheaf J _ ⋙ (evaluation Cᵒᵖ _).obj (op V)
  let q : Types.PullbackObj (φ.hom.app (op V)) (φ.hom.app (op V)) := ⟨⟨t₁, t₂⟩, heq⟩
  let q' : pullback (φ.hom.app (op V)) (φ.hom.app (op V)) :=
    (Types.pullbackIsoPullback _ _).inv q
  let i : H.obj (pullback φ φ) ≅ pullback (H.map φ) (H.map φ) :=
    PreservesPullback.iso H φ φ
  refine ⟨i.inv q', ?_, ?_⟩
  · have h1 := congrArg (· q') (PreservesPullback.iso_inv_fst H φ φ)
    simpa [H, i, q', q, Types.pullbackIsoPullback_inv_fst_apply] using h1
  · have h1 := congrArg (· q') (PreservesPullback.iso_inv_snd H φ φ)
    simpa [H, i, q', q, Types.pullbackIsoPullback_inv_snd_apply] using h1

/-- Two sections of `F` with equal images in `G` are sent to the same section
of `c.pt` by the cofork map `c.π`. -/
lemma cofork_lift_independent {F G : Sheaf J (Type max v u)} (φ : F ⟶ G)
    (c : Cofork (pullback.fst φ φ) (pullback.snd φ φ))
    {V : C} {t₁ t₂ : F.obj.obj (op V)}
    (heq : φ.hom.app (op V) t₁ = φ.hom.app (op V) t₂) :
    c.π.hom.app (op V) t₁ = c.π.hom.app (op V) t₂ := by
  obtain ⟨p, hp1, hp2⟩ := exists_pullback_section J φ t₁ t₂ heq
  have happ :
      c.π.hom.app (op V) ((pullback.fst φ φ).hom.app (op V) p) =
      c.π.hom.app (op V) ((pullback.snd φ φ).hom.app (op V) p) :=
    show ((pullback.fst φ φ) ≫ c.π).hom.app (op V) p =
         ((pullback.snd φ φ) ≫ c.π).hom.app (op V) p by rw [c.condition]
  rwa [hp1, hp2] at happ

/-- The images under `c.π` of a family of local lifts of `s` glue to a section of `c.pt`
over `U`. -/
lemma amalgamate_exists
    {F G : Sheaf J (Type max v u)} (φ : F ⟶ G)
    (c : Cofork (pullback.fst φ φ) (pullback.snd φ φ))
    {U : C} (s : G.obj.obj (op U))
    (S : Sieve U) (hS : S ∈ J U)
    (t : ∀ ⦃V : C⦄ (f : V ⟶ U), S f → F.obj.obj (op V))
    (ht : ∀ ⦃V : C⦄ (f : V ⟶ U) (hf : S f),
      φ.hom.app (op V) (t f hf) = G.obj.map f.op s) :
    ∃ x : c.pt.obj.obj (op U),
      ∀ ⦃V : C⦄ (f : V ⟶ U) (hf : S f),
        c.pt.obj.map f.op x = c.π.hom.app (op V) (t f hf) := by
  have hsf : Presieve.IsSheafFor c.pt.obj S.arrows :=
    Presheaf.IsSheaf.isSheafFor c.pt.property S hS
  let fam' : Presieve.FamilyOfElements c.pt.obj S.arrows :=
    fun _ f hf => c.π.hom.app (op _) (t f hf)
  have hcompat' : fam'.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W f g hf
    have hnat : c.π.hom.app (op W) (F.obj.map g.op (t f hf))
              = c.pt.obj.map g.op (c.π.hom.app (op V) (t f hf)) :=
      NatTrans.naturality_apply c.π.hom g.op (t f hf)
    rw [← hnat]
    apply cofork_lift_independent J φ c
    have hnatφ : φ.hom.app (op W) (F.obj.map g.op (t f hf))
               = G.obj.map g.op (φ.hom.app (op V) (t f hf)) :=
      NatTrans.naturality_apply φ.hom g.op (t f hf)
    rw [hnatφ, ht f hf, ht (g ≫ f) (S.downward_closed hf g),
        ← Functor.map_comp_apply]
    rfl
  obtain ⟨x, hx, _⟩ := hsf fam' hcompat'
  exact ⟨x, fun _ f hf => hx f hf⟩

/-- If a section `x` of `c.pt` restricts to the images under `c.π` of a family of local lifts
of `s`, then it restricts to the image under `c.π` of *any* lift `t'` of any restriction
`G.map f s`. -/
lemma universal_from_local
    {F G : Sheaf J (Type max v u)} (φ : F ⟶ G)
    (c : Cofork (pullback.fst φ φ) (pullback.snd φ φ))
    {U : C} (s : G.obj.obj (op U))
    (S : Sieve U) (hS : S ∈ J U)
    (t : ∀ ⦃V : C⦄ (f : V ⟶ U), S f → F.obj.obj (op V))
    (ht : ∀ ⦃V : C⦄ (f : V ⟶ U) (hf : S f),
      φ.hom.app (op V) (t f hf) = G.obj.map f.op s)
    (x : c.pt.obj.obj (op U))
    (hx : ∀ ⦃V : C⦄ (f : V ⟶ U) (hf : S f),
      c.pt.obj.map f.op x = c.π.hom.app (op V) (t f hf)) :
    ∀ ⦃V : C⦄ (f : V ⟶ U) (t' : F.obj.obj (op V)),
      φ.hom.app (op V) t' = G.obj.map f.op s →
      c.pt.obj.map f.op x = c.π.hom.app (op V) t' := by
  intro V f t' ht'
  apply sheaf_separated J c.pt (J.pullback_stable f hS)
  intro W g hg
  have lhs : c.pt.obj.map g.op (c.pt.obj.map f.op x)
           = c.pt.obj.map (g ≫ f).op x := by
    rw [← Functor.map_comp_apply]
    rfl
  have rhs : c.pt.obj.map g.op (c.π.hom.app (op V) t')
           = c.π.hom.app (op W) (F.obj.map g.op t') :=
    (NatTrans.naturality_apply c.π.hom g.op t').symm
  have eq_phi : φ.hom.app (op W) (t (g ≫ f) hg)
              = φ.hom.app (op W) (F.obj.map g.op t') := by
    rw [ht (g ≫ f) hg, NatTrans.naturality_apply φ.hom g.op t', ht',
        ← Functor.map_comp_apply]
    rfl
  rw [lhs, hx (g ≫ f) hg, rhs, cofork_lift_independent J φ c eq_phi]

/-- For a section `s` of `G` there is a section `x` of `c.pt` whose restrictions are the images
under `c.π` of all lifts of the restrictions of `s`. -/
lemma descSection_exists
    {F G : Sheaf J (Type max v u)} (φ : F ⟶ G) (hφ : IsSurjectiveSheafType J φ)
    (c : Cofork (pullback.fst φ φ) (pullback.snd φ φ))
    (U : C) (s : G.obj.obj (op U)) :
    ∃ x : c.pt.obj.obj (op U),
      ∀ ⦃V : C⦄ (f : V ⟶ U) (t : F.obj.obj (op V)),
        φ.hom.app (op V) t = G.obj.map f.op s →
        c.pt.obj.map f.op x = c.π.hom.app (op V) t := by
  obtain ⟨S, hS, hlift⟩ := hφ s
  let t : ∀ ⦃V : C⦄ (f : V ⟶ U), S f → F.obj.obj (op V) :=
    fun _ f hf => (hlift f hf).choose
  have ht : ∀ ⦃V : C⦄ (f : V ⟶ U) (hf : S f),
      φ.hom.app (op V) (t f hf) = G.obj.map f.op s :=
    fun _ f hf => (hlift f hf).choose_spec
  obtain ⟨x, hx⟩ := amalgamate_exists J φ c s S hS t ht
  exact ⟨x, universal_from_local J φ c s S hS t ht x hx⟩

/-- A section of `c.pt` whose restrictions are the images under `c.π` of all lifts of the
restrictions of a section `s` of `G` is unique. -/
lemma descSection_unique
    {F G : Sheaf J (Type max v u)} (φ : F ⟶ G) (hφ : IsSurjectiveSheafType J φ)
    (c : Cofork (pullback.fst φ φ) (pullback.snd φ φ))
    {U : C} (s : G.obj.obj (op U))
    {x y : c.pt.obj.obj (op U)}
    (hx : ∀ ⦃V : C⦄ (f : V ⟶ U) (t : F.obj.obj (op V)),
        φ.hom.app (op V) t = G.obj.map f.op s →
        c.pt.obj.map f.op x = c.π.hom.app (op V) t)
    (hy : ∀ ⦃V : C⦄ (f : V ⟶ U) (t : F.obj.obj (op V)),
        φ.hom.app (op V) t = G.obj.map f.op s →
        c.pt.obj.map f.op y = c.π.hom.app (op V) t) :
    x = y := by
  obtain ⟨S, hS, hlift⟩ := hφ s
  refine sheaf_separated J c.pt hS x y ?_
  intro V f hf
  obtain ⟨t, ht⟩ := hlift f hf
  rw [hx f t ht, hy f t ht]

/-- For a surjection `φ`, every cofork map `c.π` factors through `φ`. -/
lemma descent_exists
    {F G : Sheaf J (Type max v u)} (φ : F ⟶ G) (hφ : IsSurjectiveSheafType J φ)
    (c : Cofork (pullback.fst φ φ) (pullback.snd φ φ)) :
    ∃ m : G ⟶ c.pt, φ ≫ m = c.π := by
  classical
  choose desc desc_spec using descSection_exists J φ hφ c
  have nat : ∀ ⦃X Y : Cᵒᵖ⦄ (h : X ⟶ Y) (s : G.obj.obj X),
      desc Y.unop (G.obj.map h s) = c.pt.obj.map h (desc X.unop s) := by
    intro X Y h s
    apply descSection_unique J φ hφ c (G.obj.map h s)
      (desc_spec Y.unop (G.obj.map h s))
    intro W f t ht
    have hcomp : φ.hom.app (op W) t = G.obj.map (h ≫ f.op) s := by simp [ht]
    have hk := desc_spec X.unop s ((h ≫ f.op).unop) t (by
      simpa [Opposite.op_unop] using hcomp)
    rw [show c.pt.obj.map f.op (c.pt.obj.map h (desc X.unop s))
          = c.pt.obj.map (h ≫ f.op) (desc X.unop s) by simp]
    exact hk
  refine ⟨⟨{ app := fun U => ↾(fun s => desc U.unop s), naturality := ?_ }⟩, ?_⟩
  · intro X Y h
    ext s
    exact nat h s
  · ext U t
    simpa using desc_spec U.unop (φ.hom.app U t) (𝟙 U.unop) t (by simp)

/-- For a surjection `φ`, a factorization of a cofork map `c.π` through `φ` is unique. -/
lemma descent_unique
    {F G : Sheaf J (Type max v u)} (φ : F ⟶ G) (hφ : IsSurjectiveSheafType J φ)
    (c : Cofork (pullback.fst φ φ) (pullback.snd φ φ))
    (m₁ m₂ : G ⟶ c.pt)
    (h₁ : φ ≫ m₁ = c.π) (h₂ : φ ≫ m₂ = c.π) :
    m₁ = m₂ := by
  apply Sheaf.hom_ext
  ext ⟨U⟩ : 2
  apply ConcreteCategory.ext
  ext s
  simp only [TypeCat.Fun.toFun_apply]
  obtain ⟨S, hSJ, hlift⟩ := hφ s
  apply sheaf_separated (J := J) c.pt hSJ
  intro V f hf
  obtain ⟨t, ht⟩ := hlift f hf
  have key : ∀ m : G ⟶ c.pt, φ ≫ m = c.π →
      c.pt.obj.map f.op (m.hom.app (op U) s) = c.π.hom.app (op V) t := by
    intro m h
    rw [← NatTrans.naturality_apply m.hom f.op s, ← ht]
    simpa using congr_arg (fun (η : F ⟶ c.pt) => η.hom.app (op V) t) h
  rw [key m₁ h₁, key m₂ h₂]

/-- A surjection `φ : F ⟶ G` of sheaves of sets on a site exhibits `G` as the coequalizer of
the two projections from the fiber product `F ×_G F`. -/
@[stacks 086K]
theorem coequalizer_of_surjection
    {F G : Sheaf J (Type max v u)} (φ : F ⟶ G) (hφ : IsSurjectiveSheafType J φ) :
    Nonempty (IsColimit (coequalizerCofork J φ)) := by
  refine ⟨Cofork.IsColimit.mk' (coequalizerCofork J φ) (fun s => ?_)⟩
  let h := descent_exists J φ hφ s
  refine ⟨h.choose, ?_, ?_⟩
  · simpa [coequalizerCofork, Cofork.π_ofπ] using h.choose_spec
  · intro m' hm'
    exact descent_unique J φ hφ s m' h.choose
      (by simpa [coequalizerCofork, Cofork.π_ofπ] using hm') h.choose_spec

end Stacks.Sites.SurjectionCoequalizer

