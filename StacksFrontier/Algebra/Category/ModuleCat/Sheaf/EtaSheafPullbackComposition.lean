module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Composition

/-!
# The comparison of décalages under a composite of pullbacks, up to an automorphism

Let `g : W ⟶ X` and `f : X ⟶ Y` be morphisms of ringed spaces, `I ⊆ 𝒪_Y`, `J ⊆ 𝒪_X` and
`K ⊆ 𝒪_W` invertible ideal sheaves, with `f^*I ≅ J`, `g^*J ≅ K` and `(g ≫ f)^*I ≅ K` compatible
with the inclusions.  For a complex `F^•` of `I`-torsion-free `𝒪_Y`-modules there are two
comparison maps

`(g ≫ f)^*(η_I F^•) ⟶ η_K((g ≫ f)^* F^•)`:

the comparison of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafPullbackTransport.lean`
for the composite, and the composite of the comparisons for `f` and for `g`, conjugated by the
pullback-composition isomorphism `(g ≫ f)^* ≅ g^* f^*`.  This file shows that they **differ by an
automorphism of the complex `η_K((g ≫ f)^* F^•)`**.

That is all that is needed to transfer the property of being an isomorphism, or a
quasi-isomorphism, between the two, and it avoids the coherence of the interchange of pullbacks
with tensor products under composition, which is not available: both comparisons act on the
projections of the fibre products defining the décalage through *some* identification of the
twisted terms, natural in the module and compatible with the inclusions of consecutive ideal
powers, and any two such identifications differ by a twist in the sense of
`Stacks.IdealTorsion.Eta.EtaTwist`.

## Main definitions

* `Stacks.IdealTorsion.Eta.PowerInterchange`: an identification `k^*(I^{⊗ n} ⊗ M) ≅
  K^{⊗ n} ⊗ k^*M`, natural in `M` and compatible with the inclusions of consecutive powers.
* `Stacks.IdealTorsion.Eta.PowerInterchange.twist`: the twist relating two of them.
* `Stacks.IdealTorsion.Eta.PowerInterchange.comp`: the interchange for a composite, built from
  the interchanges for the two factors and the pullback-composition isomorphism.

## Main results

* `Stacks.IdealTorsion.Eta.PowerInterchange.eq_comp_iso_hom`: two maps into a décalage acting on
  the projections through two interchanges differ by the induced automorphism.
* `Stacks.IdealTorsion.Eta.transportedPullbackEtaMap_comp`: **the comparison for a composite is
  the composite of the comparisons, up to an automorphism of the target.**
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)

universe u

namespace Stacks.IdealTorsion.Eta

/-! ### Squares of isomorphisms in an abstract category

The décalage files mix several definitionally equal spellings of the structure sheaf of rings, so
`rw` does not act on the composites below.  The bookkeeping is done once here, in an abstract
category, and applied by `exact`, where the spellings are identified at `default`
transparency. -/

section Squares

variable {C : Type*} [Category C]

/-- A square with isomorphisms as its horizontal sides, read through their inverses. -/
theorem square_inv {A B A' B' : C} {x : A ⟶ A'} {y : B ⟶ B'} (e₁ : A ≅ B) (e₂ : A' ≅ B')
    (h : x ≫ e₂.hom = e₁.hom ≫ y) : y ≫ e₂.inv = e₁.inv ≫ x := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Pasting a square read through inverses with a square read forwards. -/
theorem square_paste {A B A' B' D D' : C} {x : B ⟶ B'} {y : A ⟶ A'} {z : D ⟶ D'}
    (e₁ : A ≅ B) (e₂ : A' ≅ B') (f₁ : A ≅ D) (f₂ : A' ≅ D')
    (h₁ : x ≫ e₂.inv = e₁.inv ≫ y) (h₂ : y ≫ f₂.hom = f₁.hom ≫ z) :
    x ≫ (e₂.inv ≫ f₂.hom) = (e₁.inv ≫ f₁.hom) ≫ z := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Two maps through the same morphism followed by two isomorphisms differ by the composite of
the second isomorphism read backwards with the first. -/
theorem eq_comp_inv_comp_hom {A B T : C} {a b : A ⟶ T} {x : A ⟶ B} (e e' : B ≅ T)
    (ha : a = x ≫ e.hom) (hb : b = x ≫ e'.hom) : a = b ≫ (e'.inv ≫ e.hom) := by
  rw [ha, hb, Category.assoc, Iso.hom_inv_id_assoc]

/-- Two projections factoring through the same maps followed by two isomorphisms differ by the
composite of the second isomorphism read backwards with the first. -/
private theorem proj_eq_comp_inv_comp_hom {A B B' D T : C} {a b : A ⟶ D} {p : D ⟶ T}
    {x : A ⟶ B} {y : B ⟶ B'} (e e' : B' ≅ T) (ha : a ≫ p = x ≫ y ≫ e.hom)
    (hb : b ≫ p = x ≫ y ≫ e'.hom) : a ≫ p = b ≫ p ≫ (e'.inv ≫ e.hom) :=
  (eq_comp_inv_comp_hom e e' (ha.trans (Category.assoc _ _ _).symm)
    (hb.trans (Category.assoc _ _ _).symm)).trans (Category.assoc _ _ _)

/-- Pasting four squares. -/
theorem square_paste₄ {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : C} {x₀ : A₀ ⟶ B₀} {x₁ : A₁ ⟶ B₁}
    {x₂ : A₂ ⟶ B₂} {x₃ : A₃ ⟶ B₃} {x₄ : A₄ ⟶ B₄}
    {a₁ : A₀ ⟶ A₁} {a₂ : A₁ ⟶ A₂} {a₃ : A₂ ⟶ A₃} {a₄ : A₃ ⟶ A₄}
    {b₁ : B₀ ⟶ B₁} {b₂ : B₁ ⟶ B₂} {b₃ : B₂ ⟶ B₃} {b₄ : B₃ ⟶ B₄}
    (h₁ : x₀ ≫ b₁ = a₁ ≫ x₁) (h₂ : x₁ ≫ b₂ = a₂ ≫ x₂) (h₃ : x₂ ≫ b₃ = a₃ ≫ x₃)
    (h₄ : x₃ ≫ b₄ = a₄ ≫ x₄) :
    x₀ ≫ (b₁ ≫ b₂ ≫ b₃ ≫ b₄) = (a₁ ≫ a₂ ≫ a₃ ≫ a₄) ≫ x₄ := by
  rw [← Category.assoc x₀, h₁, Category.assoc, ← Category.assoc x₁, h₂, Category.assoc,
    ← Category.assoc x₂, h₃, Category.assoc, h₄]
  simp only [Category.assoc]

/-- A functor carries a commutative square to a commutative square. -/
theorem functor_square {D : Type*} [Category D] (G : C ⥤ D) {A B A' B' : C} {x : A ⟶ B}
    {y : B ⟶ B'} {z : A ⟶ A'} {w : A' ⟶ B'} (h : x ≫ y = z ≫ w) :
    G.map x ≫ G.map y = G.map z ≫ G.map w := by
  rw [← G.map_comp, h, G.map_comp]

/-- The composite of four maps through a sequence of pasted squares: the projection of a
composite comparison. -/
theorem comp_chain₄ {A₀ A₁ A₂ A₃ A₄ P₀ P₁ P₂ P₃ P₄ : C}
    {m₁ : A₀ ⟶ A₁} {m₂ : A₁ ⟶ A₂} {m₃ : A₂ ⟶ A₃} {m₄ : A₃ ⟶ A₄}
    {p₀ : A₀ ⟶ P₀} {p₁ : A₁ ⟶ P₁} {p₂ : A₂ ⟶ P₂} {p₃ : A₃ ⟶ P₃} {p₄ : A₄ ⟶ P₄}
    {q₁ : P₀ ⟶ P₁} {q₂ : P₁ ⟶ P₂} {q₃ : P₂ ⟶ P₃} {q₄ : P₃ ⟶ P₄}
    (h₁ : m₁ ≫ p₁ = p₀ ≫ q₁) (h₂ : m₂ ≫ p₂ = p₁ ≫ q₂) (h₃ : m₃ ≫ p₃ = p₂ ≫ q₃)
    (h₄ : m₄ ≫ p₄ = p₃ ≫ q₄) :
    (m₁ ≫ m₂ ≫ m₃ ≫ m₄) ≫ p₄ = p₀ ≫ (q₁ ≫ q₂ ≫ q₃ ≫ q₄) := by
  simp only [Category.assoc]
  rw [h₄, ← Category.assoc m₃, h₃, Category.assoc, ← Category.assoc m₂, h₂, Category.assoc,
    ← Category.assoc m₁, h₁, Category.assoc]

end Squares

section Interchange

variable {W Y : RingedSpace.{u}} (k : W ⟶ Y)
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  (K : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
  (κ : K ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
  [Stacks.SheafOfModules.IsInvertible W.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf).property K]

/-- **An interchange of the pullback along `k` with the integer ideal powers**: isomorphisms
`k^*(I^{⊗ n} ⊗ M) ≅ K^{⊗ n} ⊗ k^*M`, natural in the module `M` and compatible with the inclusions
of consecutive ideal powers. -/
structure PowerInterchange where
  /-- The isomorphisms. -/
  iso : ∀ (n : ℤ) (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)),
    Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
      ((pullbackFunctor k).obj (idealPowerTerm Y I n M))
      (idealPowerTerm W K n ((pullbackFunctor k).obj M))
  /-- Naturality in the module. -/
  natural : ∀ (n : ℤ) {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)}
    (a : M ⟶ N), (pullbackFunctor k).map (idealPowerMap Y I n a) ≫ (iso n N).hom =
      (iso n M).hom ≫ idealPowerMap W K n ((pullbackFunctor k).map a)
  /-- Compatibility with the inclusions of consecutive ideal powers. -/
  incl : ∀ (n : ℤ) (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)),
    (pullbackFunctor k).map (idealPowerIncl Y I ι n M) ≫ (iso n M).hom =
      (iso (n + 1) M).hom ≫ idealPowerIncl W K κ n ((pullbackFunctor k).obj M)

namespace PowerInterchange

variable {k I ι K κ}

/-- Naturality, read through the inverses. -/
theorem natural_inv (E : PowerInterchange k I ι K κ) (n : ℤ)
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)} (a : M ⟶ N) :
    idealPowerMap W K n ((pullbackFunctor k).map a) ≫ (E.iso n N).inv =
      (E.iso n M).inv ≫ (pullbackFunctor k).map (idealPowerMap Y I n a) :=
  square_inv (E.iso n M) (E.iso n N) (E.natural n a)

/-- Compatibility with the inclusions, read through the inverses. -/
theorem incl_inv (E : PowerInterchange k I ι K κ) (n : ℤ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    idealPowerIncl W K κ n ((pullbackFunctor k).obj M) ≫ (E.iso n M).inv =
      (E.iso (n + 1) M).inv ≫ (pullbackFunctor k).map (idealPowerIncl Y I ι n M) :=
  square_inv (E.iso (n + 1) M) (E.iso n M) (E.incl n M)

variable (F : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)

/-- **The twist relating two interchanges**, on the cospans defining the décalage of the pulled
back complex: in each twisted term it is the second interchange read backwards followed by the
first. -/
def twist (E E' : PowerInterchange k I ι K κ) : EtaTwist W K κ (pullbackComplex k F) where
  cur n := (E'.iso n (F.X n)).symm ≪≫ E.iso n (F.X n)
  nxt n := (E'.iso n (F.X (n + 1))).symm ≪≫ E.iso n (F.X (n + 1))
  map_comm n := by
    change idealPowerMap W K n ((pullbackFunctor k).map (F.d n (n + 1))) ≫
        ((E'.iso n (F.X (n + 1))).inv ≫ (E.iso n (F.X (n + 1))).hom) =
      ((E'.iso n (F.X n)).inv ≫ (E.iso n (F.X n)).hom) ≫
        idealPowerMap W K n ((pullbackFunctor k).map (F.d n (n + 1)))
    exact square_paste _ _ _ _ (E'.natural_inv n (F.d n (n + 1))) (E.natural n (F.d n (n + 1)))
  incl_comm n := by
    change idealPowerIncl W K κ n ((pullbackFunctor k).obj (F.X (n + 1))) ≫
        ((E'.iso n (F.X (n + 1))).inv ≫ (E.iso n (F.X (n + 1))).hom) =
      ((E'.iso (n + 1) (F.X (n + 1))).inv ≫ (E.iso (n + 1) (F.X (n + 1))).hom) ≫
        idealPowerIncl W K κ n ((pullbackFunctor k).obj (F.X (n + 1)))
    exact square_paste _ _ _ _ (E'.incl_inv n (F.X (n + 1))) (E.incl n (F.X (n + 1)))

/-- **Two maps into a décalage acting on the projections through two interchanges differ by the
induced automorphism.** -/
theorem eq_comp_iso_hom (E E' : PowerInterchange k I ι K κ) [Mono κ]
    (hF : ∀ n : ℤ, IsIdealTorsionFree W κ ((pullbackComplex k F).X n))
    {S : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf)) ℤ}
    (s : ∀ n : ℤ, S.X n ⟶ (pullbackFunctor k).obj (etaTerm Y I ι F n))
    (a b : S ⟶ etaObj W K κ (pullbackComplex k F) hF)
    (ha : ∀ n : ℤ, a.f n ≫ etaFst W K κ (pullbackComplex k F) n =
      s n ≫ (pullbackFunctor k).map (etaFst Y I ι F n) ≫ (E.iso n (F.X n)).hom)
    (ha' : ∀ n : ℤ, a.f n ≫ etaSnd W K κ (pullbackComplex k F) n =
      s n ≫ (pullbackFunctor k).map (etaSnd Y I ι F n) ≫ (E.iso (n + 1) (F.X (n + 1))).hom)
    (hb : ∀ n : ℤ, b.f n ≫ etaFst W K κ (pullbackComplex k F) n =
      s n ≫ (pullbackFunctor k).map (etaFst Y I ι F n) ≫ (E'.iso n (F.X n)).hom)
    (hb' : ∀ n : ℤ, b.f n ≫ etaSnd W K κ (pullbackComplex k F) n =
      s n ≫ (pullbackFunctor k).map (etaSnd Y I ι F n) ≫ (E'.iso (n + 1) (F.X (n + 1))).hom) :
    a = b ≫ ((twist F E E').iso hF).hom := by
  refine EtaTwist.eq_comp_iso_hom hF (twist F E E') a b (fun n => ?_) (fun n => ?_)
  · exact proj_eq_comp_inv_comp_hom (E.iso n (F.X n)) (E'.iso n (F.X n)) (ha n) (hb n)
  · exact proj_eq_comp_inv_comp_hom (E.iso (n + 1) (F.X (n + 1))) (E'.iso (n + 1) (F.X (n + 1)))
      (ha' n) (hb' n)

end PowerInterchange

/-- The interchange of the pullback with the ideal powers, transported along a compatible
identification `e : k^*I ≅ K`: `Stacks.IdealTorsion.Eta.pullbackIdealPowerTransportIso`. -/
def transportInterchange
    (e : Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
      ((pullbackFunctor k).obj I) K)
    (he : e.hom ≫ κ = pullbackIdealIncl k I ι) : PowerInterchange k I ι K κ where
  iso := pullbackIdealPowerTransportIso k I K e
  natural n _ _ a := pullbackIdealPowerTransportIso_natural k I K e n a
  incl n M := pullbackIdealPowerTransportIso_idealPowerIncl k I ι K κ e he n M

end Interchange

/-! ### The interchange for a composite -/

section Composite

variable {W X Y : RingedSpace.{u}} (g : W ⟶ X) (f : X ⟶ Y)
  {I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)}
  {ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)}
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  {J : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)}
  {κ : J ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)}
  [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property J]
  {K : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf)}
  {κ' : K ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf)}
  [Stacks.SheafOfModules.IsInvertible W.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf).property K]

/-- The pullback-composition isomorphism `(g ≫ f)^* M ≅ g^*(f^* M)`. -/
def pullbackCompIso (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
      ((pullbackFunctor (g ≫ f)).obj M) ((pullbackFunctor g).obj ((pullbackFunctor f).obj M)) :=
  ((Stacks.DerivedPullback.Composition.modulePullbackComp g f).app M).symm

/-- The pullback-composition isomorphism is natural. -/
theorem pullbackCompIso_natural
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)} (a : M ⟶ N) :
    (pullbackFunctor (g ≫ f)).map a ≫ (pullbackCompIso g f N).hom =
      (pullbackCompIso g f M).hom ≫ (pullbackFunctor g).map ((pullbackFunctor f).map a) :=
  (Stacks.DerivedPullback.Composition.modulePullbackComp g f).inv.naturality a

/-- The pullback-composition isomorphism on complexes. -/
def pullbackComplexCompIso
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ) :
    pullbackComplex (g ≫ f) F ≅ pullbackComplex g (pullbackComplex f F) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => pullbackCompIso g f (F.X n))
    (fun n m _ => (pullbackCompIso_natural g f (F.d n m)).symm)

/-- The degree `n` component of `(pullbackComplexCompIso g f F).hom` is
`(pullbackCompIso g f (F.X n)).hom`. -/
theorem pullbackComplexCompIso_hom_f
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) : (pullbackComplexCompIso g f F).hom.f n = (pullbackCompIso g f (F.X n)).hom := rfl

/-- The degree `n` component of `(pullbackComplexCompIso g f F).inv` is
`(pullbackCompIso g f (F.X n)).inv`. -/
theorem pullbackComplexCompIso_inv_f
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) : (pullbackComplexCompIso g f F).inv.f n = (pullbackCompIso g f (F.X n)).inv := rfl

/-- An integer ideal power applied to an isomorphism of modules. -/
def idealPowerMapIso (Z : RingedSpace.{u})
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).property L] (n : ℤ)
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)} (e : M ≅ N) :
    idealPowerTerm Z L n M ≅ idealPowerTerm Z L n N where
  hom := idealPowerMap Z L n e.hom
  inv := idealPowerMap Z L n e.inv
  hom_inv_id := by rw [← idealPowerMap_comp, e.hom_inv_id, idealPowerMap_id]
  inv_hom_id := by rw [← idealPowerMap_comp, e.inv_hom_id, idealPowerMap_id]

variable {g f}

/-- **The interchange for a composite**, built from the interchanges for the two factors and the
pullback-composition isomorphism:
`(g ≫ f)^*(I^n ⊗ M) ≅ g^* f^*(I^n ⊗ M) ≅ g^*(J^n ⊗ f^*M) ≅ K^n ⊗ g^* f^* M ≅ K^n ⊗ (g ≫ f)^*M`. -/
def PowerInterchange.comp (Ef : PowerInterchange f I ι J κ) (Eg : PowerInterchange g J κ K κ') :
    PowerInterchange (g ≫ f) I ι K κ' where
  iso n M := pullbackCompIso g f (idealPowerTerm Y I n M) ≪≫
    (pullbackFunctor g).mapIso (Ef.iso n M) ≪≫ Eg.iso n ((pullbackFunctor f).obj M) ≪≫
    idealPowerMapIso W K n (pullbackCompIso g f M).symm
  natural n M N a := square_paste₄ (pullbackCompIso_natural g f (idealPowerMap Y I n a))
    (functor_square (pullbackFunctor g) (Ef.natural n a))
    (Eg.natural n ((pullbackFunctor f).map a))
    ((idealPowerMap_comp W K n _ _).symm.trans
      ((congrArg (idealPowerMap W K n) (square_inv (pullbackCompIso g f M)
        (pullbackCompIso g f N) (pullbackCompIso_natural g f a))).trans
        (idealPowerMap_comp W K n _ _)))
  incl n M := square_paste₄ (pullbackCompIso_natural g f (idealPowerIncl Y I ι n M))
    (functor_square (pullbackFunctor g) (Ef.incl n M))
    (Eg.incl n ((pullbackFunctor f).obj M))
    (idealPowerIncl_natural W K κ' n (pullbackCompIso g f M).inv)

/-! ### The comparison for a composite -/

variable (g f) [Mono ι] [Mono κ] [Mono κ']
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
    (pullbackIdealIncl g J κ)]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
    (pullbackIdealIncl (g ≫ f) I ι)]
  (ef : Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    ((pullbackFunctor f).obj I) J) (hef : ef.hom ≫ κ = pullbackIdealIncl f I ι)
  (eg : Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
    ((pullbackFunctor g).obj J) K) (heg : eg.hom ≫ κ' = pullbackIdealIncl g J κ)
  (egf : Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
    ((pullbackFunctor (g ≫ f)).obj I) K) (hegf : egf.hom ≫ κ' = pullbackIdealIncl (g ≫ f) I ι)
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
  (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
  (hFf' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
  (hFf : ∀ n : ℤ, IsIdealTorsionFree X κ ((pullbackComplex f F).X n))
  (hFg' : ∀ n : ℤ, IsIdealTorsionFree W (pullbackIdealIncl g J κ)
    ((pullbackComplex g (pullbackComplex f F)).X n))
  (hFg : ∀ n : ℤ, IsIdealTorsionFree W κ' ((pullbackComplex g (pullbackComplex f F)).X n))
  (hFgf' : ∀ n : ℤ, IsIdealTorsionFree W (pullbackIdealIncl (g ≫ f) I ι)
    ((pullbackComplex (g ≫ f) F).X n))
  (hFgf : ∀ n : ℤ, IsIdealTorsionFree W κ' ((pullbackComplex (g ≫ f) F).X n))

/-- **The composite of the comparisons for `f` and for `g`**, conjugated by the
pullback-composition isomorphism:
`(g ≫ f)^*(η_I F) ≅ g^* f^*(η_I F) ⟶ g^*(η_J f^*F) ⟶ η_K(g^* f^* F) ≅ η_K((g ≫ f)^*F)`. -/
def compositePullbackEtaMap :
    pullbackComplex (g ≫ f) (etaObj Y I ι F hF) ⟶
      etaObj W K κ' (pullbackComplex (g ≫ f) F) hFgf :=
  (pullbackComplexCompIso g f (etaObj Y I ι F hF)).hom ≫
    pullbackComplexMap g (transportedPullbackEtaMap f I ι J κ ef hef F hF hFf' hFf) ≫
    transportedPullbackEtaMap g J κ K κ' eg heg (pullbackComplex f F) hFf hFg' hFg ≫
    etaMap W K κ' (pullbackComplexCompIso g f F).inv hFg hFgf

/-- **The comparison for a composite is the composite of the comparisons, up to an automorphism of
the target.**  Both act on the projections of the fibre products through an interchange of the
pullback along `g ≫ f` with the ideal powers — the transported one for the composite, and the
composite one of `Stacks.IdealTorsion.Eta.PowerInterchange.comp` — so they differ by the twist
relating the two. -/
theorem transportedPullbackEtaMap_comp :
    transportedPullbackEtaMap (g ≫ f) I ι K κ' egf hegf F hF hFgf' hFgf =
      compositePullbackEtaMap g f ef hef eg heg F hF hFf' hFf hFg' hFg hFgf ≫
        ((PowerInterchange.twist F (transportInterchange (g ≫ f) I ι K κ' egf hegf)
          ((transportInterchange f I ι J κ ef hef).comp
            (transportInterchange g J κ K κ' eg heg))).iso hFgf).hom := by
  refine PowerInterchange.eq_comp_iso_hom F _ _ hFgf (fun n => 𝟙 _) _ _
    (fun n => (transportedPullbackEtaMap_f_fst (g ≫ f) I ι K κ' egf hegf F hF hFgf' hFgf n).trans
      (Category.id_comp _).symm)
    (fun n => (transportedPullbackEtaMap_f_snd (g ≫ f) I ι K κ' egf hegf F hF hFgf' hFgf n).trans
      (Category.id_comp _).symm)
    (fun n => ?_) (fun n => ?_)
  · exact (comp_chain₄ (pullbackCompIso_natural g f (etaFst Y I ι F n)).symm
      (functor_square (pullbackFunctor g)
        (transportedPullbackEtaMap_f_fst f I ι J κ ef hef F hF hFf' hFf n))
      (transportedPullbackEtaMap_f_fst g J κ K κ' eg heg (pullbackComplex f F) hFf hFg' hFg n)
      (etaMap_fst W K κ' (pullbackComplexCompIso g f F).inv hFg hFgf n)).trans
      (Category.id_comp _).symm
  · exact (comp_chain₄ (pullbackCompIso_natural g f (etaSnd Y I ι F n)).symm
      (functor_square (pullbackFunctor g)
        (transportedPullbackEtaMap_f_snd f I ι J κ ef hef F hF hFf' hFf n))
      (transportedPullbackEtaMap_f_snd g J κ K κ' eg heg (pullbackComplex f F) hFf hFg' hFg n)
      (etaMap_snd W K κ' (pullbackComplexCompIso g f F).inv hFg hFgf n)).trans
      (Category.id_comp _).symm

end Composite

end Stacks.IdealTorsion.Eta

end
