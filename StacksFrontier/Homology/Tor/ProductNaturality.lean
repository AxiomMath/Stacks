module

public import StacksFrontier.Homology.Tor.CrossProduct

/-!
# Naturality of the tensoring of cohomology classes

Let `R` be a commutative ring.  The tensoring of cohomology classes of Tag 068H,
`RingTheory.TorProducts.cohomologyTensorProduct`, is a map

`Hⁱ(K) ⊗_R Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗^𝐋_R L)`

for `K, L ∈ D(R)`, and the source states it as a construction on cocycles of K-flat
representatives.  This file records that it is *natural*: for morphisms `u : K ⟶ K'` and
`v : L ⟶ L'` of `D(R)` the square relating `Hⁱ(u) ⊗ Hʲ(v)` to `Hⁱ⁺ʲ(u ⊗ v)` commutes, provided
`K` and `L` are represented by K-projective K-flat complexes.

## Main results

* `RingTheory.TorProducts.cohomologyTensorProduct_naturality_of_isKProjective` — the naturality
  square, for `K = Q(P₀)` and `L = Q(Q₀)` with `P₀` and `Q₀` K-projective and K-flat.

## Implementation notes

*Why K-projectivity of the source.*  `cohomologyTensorProduct K L i j` is built from a choice of
K-flat representatives of `K` and of `L`, and it is characterised by the cocycle formula
Equation 15.64.0.1 at that choice (`cohomologyTensorProduct_map_cocycles`).  Comparing the
formula at the choice made for `K` with the one made for `K'` requires lifting `u` to a morphism
of complexes, and a morphism of `D(R)` out of `Q(P₀)` is `Q` of a morphism of complexes exactly
when `P₀` is K-projective
(`TorCrossProduct.exists_lift_of_isKProjective`).  With that lift, both sides of the square are
computed on cocycles and compared by
`TorCrossProduct.cohomologyTensorProduct_map_eq_of_isKProjective`, which says the cocycle
formula also holds at the given K-projective K-flat pair and not only at the chosen one.

This is the generality the cup product with a cohomology class needs: there the sources are the
shifted free modules `A[-i]`, which are single complexes of a free module and so both
K-projective and K-flat.  No naturality at an arbitrary source is claimed.

## References

* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Category
open CochainComplex.DerivedTensor

universe u

namespace RingTheory.TorProducts

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- Substituting a commuting square into the middle of a composite, with every object and
morphism a variable.

The naturality square used below crosses two spellings of one object, so the composite it has to
be substituted into is associated the way the ambient goal happens to be associated rather than
the way `reassoc_of%` normalises it.  With the factors as variables the reassociation is a plain
rewrite, and the crossing is spent once, on `exact`, at `default` transparency. -/
private lemma comp_square_comp {D : Type*} [Category D] {A B₁ B₂ B₃ T E : D}
    (f : A ⟶ B₁) {g : B₁ ⟶ B₂} {h : B₂ ⟶ T} {g' : B₁ ⟶ B₃} {h' : B₃ ⟶ T} (t : T ⟶ E)
    (e : g ≫ h = g' ≫ h') :
    f ≫ g ≫ h ≫ t = f ≫ g' ≫ h' ≫ t := by
  rw [reassoc_of% e]

/-- The bookkeeping of the naturality argument, with every object and morphism a variable.

It is stated abstractly on purpose, and with each composite broken into its factors.  The
concrete morphisms below compose `homologyπ`, whose codomain is spelled `K.homology i`, with a
component of `homologyFunctorFactors`, whose domain is spelled
`(homologyFunctor _ _ i).obj K`; those are the same object but not the same term, so `rw`,
`simp only` and even `dsimp only` reject the composite at `implicit` transparency and refuse to
fire.  Here the factors are variables, so associativity is a plain rewrite.

The data are: the two cocycle formulas `hE` and `hE₀` of Tag 068H at the two pairs of
representatives; the comparison `hLu`, `hLv` of a class with its image under a lift, in each
tensor factor; the compatibility `hcyc` of the tensoring of cocycles with the lifts and the
naturality `hπ` of `homologyπ`; and the two halves `hmor`, `hnatL` of the comparison of the two
K-flat comparisons. -/
private lemma naturality_cancel {C : Type*} [Category C] [MonoidalCategory C]
    {C₁ : Type*} [Category C₁] (F : C₁ ⥤ C)
    {cy₀ ho₀ hk hK cy ho hkP : C} {cy₀' ho₀' hk' hK' cy' ho' hkP' : C}
    {d d₀ zc zc₀ : C} {o o₀ kk kk₀ : C₁}
    {p₁ : cy₀ ⟶ ho₀} {ι₁ : ho₀ ⟶ hk} {w₁ : hk ⟶ hK}
    {c₁ : cy₀ ⟶ cy} {q₁ : cy ⟶ ho} {j₁ : ho ⟶ hkP} {e₁ : hkP ⟶ hK}
    {p₂ : cy₀' ⟶ ho₀'} {ι₂ : ho₀' ⟶ hk'} {w₂ : hk' ⟶ hK'}
    {c₂ : cy₀' ⟶ cy'} {q₂ : cy' ⟶ ho'} {j₂ : ho' ⟶ hkP'} {e₂ : hkP' ⟶ hK'}
    {Am : hK ⊗ hK' ⟶ F.obj o} {A₀ : hk ⊗ hk' ⟶ F.obj o₀}
    {Vm : o₀ ⟶ o} {bigm : o ⟶ kk} {cmp0 : o₀ ⟶ kk₀} {qab : kk₀ ⟶ kk}
    {hffP : F.obj kk ⟶ d} {hffP₀ : F.obj kk₀ ⟶ d₀} {mm : d₀ ⟶ d}
    {z : cy ⊗ cy' ⟶ zc} {z₀ : cy₀ ⊗ cy₀' ⟶ zc₀} {pq : zc ⟶ d} {pq₀ : zc₀ ⟶ d₀}
    {cm : zc₀ ⟶ zc}
    (hLu : c₁ ≫ q₁ ≫ j₁ ≫ e₁ = p₁ ≫ ι₁ ≫ w₁)
    (hLv : c₂ ≫ q₂ ≫ j₂ ≫ e₂ = p₂ ≫ ι₂ ≫ w₂)
    (hE : (q₁ ⊗ₘ q₂) ≫ (j₁ ⊗ₘ j₂) ≫ (e₁ ⊗ₘ e₂) ≫ Am ≫ F.map bigm ≫ hffP = z ≫ pq)
    (hE₀ : (p₁ ⊗ₘ p₂) ≫ (ι₁ ⊗ₘ ι₂) ≫ A₀ ≫ F.map cmp0 ≫ hffP₀ = z₀ ≫ pq₀)
    (hcyc : (c₁ ⊗ₘ c₂) ≫ z = z₀ ≫ cm)
    (hπ : cm ≫ pq = pq₀ ≫ mm)
    (hmor : Vm ≫ bigm = cmp0 ≫ qab)
    (hnatL : F.map qab ≫ hffP = hffP₀ ≫ mm)
    (hp : Epi (p₁ ⊗ₘ p₂)) (hι₁ : IsIso ι₁) (hι₂ : IsIso ι₂)
    (hGb : IsIso (F.map bigm ≫ hffP)) :
    (w₁ ⊗ₘ w₂) ≫ Am = A₀ ≫ F.map Vm := by
  have := hp
  have := hι₁
  have := hι₂
  have := hGb
  have : Epi (ι₁ ⊗ₘ ι₂) := by
    have h : ι₁ ⊗ₘ ι₂ = (asIso ι₁ ⊗ᵢ asIso ι₂).hom := rfl
    rw [h]
    infer_instance
  have hstep : (p₁ ⊗ₘ p₂) ≫ (ι₁ ⊗ₘ ι₂) ≫ (w₁ ⊗ₘ w₂) =
      (c₁ ⊗ₘ c₂) ≫ (q₁ ⊗ₘ q₂) ≫ (j₁ ⊗ₘ j₂) ≫ (e₁ ⊗ₘ e₂) := by
    simp only [tensorHom_comp_tensorHom, hLu, hLv]
  have hdagger : F.map Vm ≫ F.map bigm ≫ hffP = (F.map cmp0 ≫ hffP₀) ≫ mm := by
    rw [← Category.assoc, ← F.map_comp, hmor, F.map_comp, Category.assoc, hnatL,
      ← Category.assoc]
  have h1 : (p₁ ⊗ₘ p₂) ≫ (ι₁ ⊗ₘ ι₂) ≫ (w₁ ⊗ₘ w₂) ≫ Am ≫ F.map bigm ≫ hffP =
      z₀ ≫ pq₀ ≫ mm := by
    rw [reassoc_of% hstep, hE, reassoc_of% hcyc, hπ]
  have h2 : (p₁ ⊗ₘ p₂) ≫ (ι₁ ⊗ₘ ι₂) ≫ A₀ ≫ F.map Vm ≫ F.map bigm ≫ hffP =
      z₀ ≫ pq₀ ≫ mm := by
    rw [hdagger, Category.assoc, reassoc_of% hE₀]
  refine (cancel_epi ((p₁ ⊗ₘ p₂) ≫ (ι₁ ⊗ₘ ι₂))).1
    ((cancel_mono (F.map bigm ≫ hffP)).1 ?_)
  simp only [Category.assoc]
  exact h1.trans h2.symm

/-- **The tensoring of classes of Tag 068H is natural at a K-projective K-flat source.**  For
`P₀` and `Q₀` K-projective and K-flat cochain complexes of `R`-modules and morphisms
`u : Q(P₀) ⟶ K` and `v : Q(Q₀) ⟶ L` of `D(R)`, tensoring the classes and then applying
`Hⁱ⁺ʲ(u ⊗ v)` is the same as applying `Hⁱ(u) ⊗ Hʲ(v)` and then tensoring the classes. -/
public theorem cohomologyTensorProduct_naturality_of_isKProjective
    (P₀ Q₀ : CochainComplex (ModuleCat.{u} R) ℤ) [P₀.IsKProjective] [Q₀.IsKProjective]
    (hP₀ : P₀.KFlat) (hQ₀ : Q₀.KFlat) {K L : DObj R}
    (u : DerivedCategory.Q.obj P₀ ⟶ K) (v : DerivedCategory.Q.obj Q₀ ⟶ L) (i j : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map u ⊗ₘ
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map v) ≫
        (cohomologyTensorProduct K L i j).map =
      (cohomologyTensorProduct (DerivedCategory.Q.obj P₀) (DerivedCategory.Q.obj Q₀) i j).map ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
          (((canonicalDerivedTensorProductFunctor R).map u).app (DerivedCategory.Q.obj Q₀) ≫
            ((canonicalDerivedTensorProductFunctor R).obj K).map v) := by
  obtain ⟨z₀, hz₀⟩ := exists_tensorCycles P₀ Q₀ i j
  obtain ⟨P, Q, hP, hQ, eP, eQ, z, hz, hE⟩ := cohomologyTensorProduct_map_cocycles K L i j
  obtain ⟨a, ha⟩ := TorCrossProduct.exists_lift_of_isKProjective P₀ P (u ≫ eP.inv)
  obtain ⟨b, hb⟩ := TorCrossProduct.exists_lift_of_isKProjective Q₀ Q (v ≫ eQ.inv)
  have hE₀ := TorCrossProduct.cohomologyTensorProduct_map_eq_of_isKProjective
    P₀ Q₀ hP₀ hQ₀ i j z₀ hz₀
  -- The class of a cocycle of `X`, pushed along a chain map `c : X ⟶ Y` and then along a
  -- morphism of `D(R)` out of `Q(Y)`, is its class pushed along the composite.
  have hleft : ∀ (X Y : CochainComplex (ModuleCat.{u} R) ℤ) (c : X ⟶ Y) (k : ℤ) {Z : DObj R}
      (w : DerivedCategory.Q.obj Y ⟶ Z),
      HomologicalComplex.cyclesMap c k ≫ Y.homologyπ k ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) k).inv.app Y ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) k).map w =
        X.homologyπ k ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) k).inv.app X ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) k).map
            (DerivedCategory.Q.map c ≫ w) := by
    intro X Y c k Z w
    rw [← HomologicalComplex.homologyπ_naturality_assoc, Functor.map_comp]
    -- The naturality of `homologyFunctorFactors.inv` at `c`, with its type written out in the
    -- spelling the goal uses.  Taken as it comes, the naturality square reads
    -- `(HomologicalComplex.homologyFunctor _ _ k).map c` and `(Q ⋙ homologyFunctor _ k).map c`,
    -- which are the goal's `homologyMap c k` and `(homologyFunctor _ k).map (Q.map c)` only
    -- definitionally; `rw` re-checks at `implicit` transparency and will not cross that, while
    -- `exact` on a fully written-out type crosses it with one unification per side.
    have hn : HomologicalComplex.homologyMap c k ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) k).inv.app Y =
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) k).inv.app X ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) k).map (DerivedCategory.Q.map c) :=
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) k).inv.naturality c
    exact comp_square_comp _ _ hn
  have hLu := hleft P₀ P a i eP.hom
  rw [eP.eq_comp_inv.1 ha] at hLu
  have hLv := hleft Q₀ Q b j eQ.hom
  rw [eQ.eq_comp_inv.1 hb] at hLv
  -- The tensoring of cocycles is compatible with the lifts.
  have hcyc : (HomologicalComplex.cyclesMap a i ⊗ₘ HomologicalComplex.cyclesMap b j) ≫ z =
      z₀ ≫ HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom a b) (i + j) := by
    -- The two steps on the tensored complex, each with its type written out in the goal's
    -- spelling.  `cyclesMap_i` at `tensorHom a b` reads its complexes off that morphism, so it
    -- arrives spelled `HomologicalComplex.tensorObj P₀ Q₀` where the goal and `hz₀` say
    -- `P₀ ⊗ Q₀`; and `ι_mapBifunctorMap` arrives spelled `ιMapBifunctor` with the index
    -- hypothesis `ComplexShape.π _ _ _ (i, j) = i + j` where the goal says `ιTensorObj` and
    -- `i + j = i + j`.  Both are definitional and neither is visible to `rw`.
    have hab : HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom a b) (i + j) ≫
          (P ⊗ Q).iCycles (i + j) =
        (P₀ ⊗ Q₀).iCycles (i + j) ≫ (HomologicalComplex.tensorHom a b).f (i + j) :=
      HomologicalComplex.cyclesMap_i _ _
    have hι : HomologicalComplex.ιTensorObj P₀ Q₀ i j (i + j) rfl ≫
          (HomologicalComplex.tensorHom a b).f (i + j) =
        ((curriedTensor (ModuleCat.{u} R)).map (a.f i)).app (Q₀.X j) ≫
          ((curriedTensor (ModuleCat.{u} R)).obj (P.X i)).map (b.f j) ≫
            HomologicalComplex.ιTensorObj P Q i j (i + j) rfl :=
      HomologicalComplex.ι_mapBifunctorMap ..
    rw [← cancel_mono ((P ⊗ Q).iCycles (i + j))]
    simp only [Category.assoc, hz]
    rw [tensorHom_comp_tensorHom_assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.cyclesMap_i, ← tensorHom_comp_tensorHom_assoc, hab,
      reassoc_of% hz₀, hι]
    simp only [curriedTensor_map_app, curriedTensor_obj_map, MonoidalCategory.tensorHom_def,
      Category.assoc]
  -- The K-flat comparison intertwines the two tensorings of the lifts.
  have hmor :
      (((canonicalDerivedTensorProductFunctor R).map u).app (DerivedCategory.Q.obj Q₀) ≫
          ((canonicalDerivedTensorProductFunctor R).obj K).map v) ≫
        (((canonicalDerivedTensorProductFunctor R).map eP.inv).app L ≫
          ((canonicalDerivedTensorProductFunctor R).obj
              (DerivedCategory.Q.obj P)).map eQ.inv ≫
            ((canonicalDerivedTensorProduct R).comparison P Q hP hQ).hom) =
      ((canonicalDerivedTensorProduct R).comparison P₀ Q₀ hP₀ hQ₀).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom a b) := by
    have hnat := (canonicalDerivedTensorProduct R).comparison_naturality a b hP₀ hP hQ₀ hQ
    have hcommute := ((canonicalDerivedTensorProductFunctor R).map eP.inv).naturality v
    rw [← hnat, ha, hb]
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rw [reassoc_of% hcommute]
  -- The comparison behind the cocycle formula at `P`, `Q` is an isomorphism.
  obtain ⟨β, hβ⟩ :
      ∃ β : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).obj
            (((canonicalDerivedTensorProductFunctor R).obj K).obj L) ≅
          (P ⊗ Q).homology (i + j),
        β.hom =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
              (((canonicalDerivedTensorProductFunctor R).map eP.inv).app L ≫
                ((canonicalDerivedTensorProductFunctor R).obj
                  (DerivedCategory.Q.obj P)).map eQ.inv ≫
                ((canonicalDerivedTensorProduct R).comparison P Q hP hQ).hom) ≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (i + j)).hom.app (P ⊗ Q) :=
    ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).mapIso
          (((canonicalDerivedTensorProductFunctor R).mapIso eP.symm).app L ≪≫
            ((canonicalDerivedTensorProductFunctor R).obj
                (DerivedCategory.Q.obj P)).mapIso eQ.symm ≪≫
              (canonicalDerivedTensorProduct R).comparison P Q hP hQ) ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (i + j)).app (P ⊗ Q), rfl⟩
  have hGb : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
      (((canonicalDerivedTensorProductFunctor R).map eP.inv).app L ≫
          ((canonicalDerivedTensorProductFunctor R).obj
            (DerivedCategory.Q.obj P)).map eQ.inv ≫
          ((canonicalDerivedTensorProduct R).comparison P Q hP hQ).hom) ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (i + j)).hom.app (P ⊗ Q)) := by
    rw [← hβ]
    exact β.isIso_hom
  exact naturality_cancel (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j))
    hLu hLv hE hE₀ hcyc (HomologicalComplex.homologyπ_naturality _ _).symm hmor
    (DerivedCategory.homologyFunctorFactors_hom_naturality
      (HomologicalComplex.tensorHom a b) (i + j))
    (epi_tensorHom _ _)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P₀).isIso_inv
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) j).app Q₀).isIso_inv hGb

end RingTheory.TorProducts

end
