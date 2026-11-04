module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionNaturality

/-!
# Abelian-sheaf functoriality of the Čech cokernel of Stacks 0G7Q

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions with `c = d + 1`, and let
`ℱ` be an `𝒪_X`-module.  The class map of [Stacks, Tag 0G7Q] lands in the elementary cokernel

`Coker(⨁ᵢ ℱ_{1…î…c} ⟶ ℱ_{1…c}) = cokernel (lastDif f ℱ)`

of the last differential of the extended alternating Čech complex of [Stacks, Tag 0G7I].  This
file shows that this cokernel is functorial in `ℱ` along an arbitrary morphism of the underlying
sheaves of abelian groups, which need not be `𝒪_X`-linear.  A morphism of abelian sheaves
`ψ : ℱ ⟶ 𝒢` acts componentwise on the ordered Čech cochain groups
`Γ(ℱ_{i₀…i_p}, V) = Γ(ℱ, V ∩ U_{i₀…i_p})`, compatibly with the Čech differentials, and so induces
a morphism of the cokernels of the last differentials.

## Main definitions

* `abelianSheaf`: the exact forgetful functor `X.Modules ⥤ Sheaf (Opens X) AddCommGrpCat`,
  namely `SheafOfModules.toSheaf` at the structure sheaf of a scheme.
* `prodTermAb`, `termAb`: the morphism of abelian sheaves induced on a term of the extended
  alternating Čech complex by a morphism of the underlying abelian sheaves of the coefficient
  modules.
* `cokernelLastDifAb`: **the induced morphism `Coker(lastDif f ℱ) ⟶ Coker(lastDif f 𝒢)` of
  sheaves of abelian groups.**

## Main results

* `ordD_ordCochainMap`: the ordered Čech differential is natural in the coefficient sheaf of
  abelian groups, with no `𝒪_X`-linearity.
* `prodTermAbApp_difSucc`, `prodTermAbApp_difZero`, `termAbApp_lastDif`: the differentials of the
  extended alternating Čech complex commute with the induced maps, sectionwise.
* `map_lastDif_comp_prodTermAb`: **the naturality square for the last differential**, in the
  category of sheaves of abelian groups on `X`.
* `map_cokernelπ_comp_cokernelLastDifAb`: **the defining property of `cokernelLastDifAb`** — it
  is compatible with the canonical epimorphisms onto the two cokernels.
* `cokernelLastDifAb_unique`: that property determines `cokernelLastDifAb`; `cokernelLastDifAb_id`
  is the resulting unitality.
* `prodTermAb_mapPresheaf`, `termAb_mapPresheaf`: for a morphism of `X.Modules` the construction
  is the image under `abelianSheaf` of the `𝒪_X`-linear map
  `Stacks.Perfect.ExtendedAlternatingCech.prodMap`.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7T](https://stacks.math.columbia.edu/tag/0G7T)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G74](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 03DA](https://stacks.math.columbia.edu/tag/03DA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.SupportedFraction
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AbelianFraction

/-! ### The exact forgetful functor to abelian sheaves -/

/-- **Forgetting the `𝒪_X`-module structure**, as a functor from `𝒪_X`-modules to sheaves of
abelian groups on the underlying space of `X`: `SheafOfModules.toSheaf` at the structure sheaf of
`X`. -/
public def abelianSheaf (X : Scheme.{u}) :
    X.Modules ⥤ Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf.{u} X.ringCatSheaf

variable {X : Scheme.{u}}

/-- Forgetting the module structure preserves finite colimits, in particular cokernels. -/
public instance abelianSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (abelianSheaf X) :=
  inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))

/-- Forgetting the module structure preserves finite limits. -/
public instance abelianSheaf_preservesFiniteLimits : PreservesFiniteLimits (abelianSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))

/-- Forgetting the module structure is additive. -/
public instance abelianSheaf_additive : (abelianSheaf X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Additive

/-- The underlying abelian sheaf of an `𝒪_X`-module is its underlying abelian presheaf. -/
public theorem abelianSheaf_obj_obj (F : X.Modules) :
    ((abelianSheaf X).obj F).obj = Scheme.Modules.presheaf F := rfl

variable {F G : X.Modules}

/-- A morphism of the underlying abelian presheaves, read as a morphism of abelian sheaves. -/
public def abHom (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).obj F ⟶ (abelianSheaf X).obj G :=
  ObjectProperty.homMk ψ

/-- The morphism of abelian presheaves underlying a morphism of abelian sheaves. -/
public theorem abHom_hom (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abHom ψ).hom = ψ := rfl

/-- Forgetting the module structure of a morphism of `𝒪_X`-modules gives its underlying morphism
of abelian presheaves. -/
public theorem abelianSheaf_map (φ : F ⟶ G) :
    (abelianSheaf X).map φ = abHom (Scheme.Modules.Hom.mapPresheaf φ) := rfl

/-! ### Sections of a morphism that need not be `𝒪_X`-linear -/

/-- The action on sections of a morphism of the underlying abelian sheaves, as an additive map.
It is *not* assumed to commute with the `𝒪_X`-action. -/
public def sectionsHom (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (V : X.Opens) : Γ(F, V) →+ Γ(G, V) :=
  AddCommGrpCat.Hom.hom (ψ.app (op V))

/-- The action on sections is the component of the morphism of presheaves. -/
public theorem sectionsHom_apply (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (V : X.Opens) (x : Γ(F, V)) : sectionsHom ψ V x = ψ.app (op V) x := rfl

/-- A morphism of abelian sheaves commutes with restriction. -/
public theorem sectionsHom_naturality (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    {W V : X.Opens} (g : W ⟶ V) (x : Γ(F, V)) :
    sectionsHom ψ W (F.presheaf.map g.op x) = G.presheaf.map g.op (sectionsHom ψ V x) := by
  have h := congr($(ψ.naturality g.op) x)
  simp only [CategoryTheory.comp_apply] at h
  simp only [sectionsHom_apply]
  exact h

/-- For a morphism of `𝒪_X`-modules the action on sections is the usual one. -/
public theorem sectionsHom_mapPresheaf (φ : F ⟶ G) (V : X.Opens) (x : Γ(F, V)) :
    sectionsHom (Scheme.Modules.Hom.mapPresheaf φ) V x = φ.app V x := rfl

section Terms

variable {c : ℕ} (f : Fin c → Γ(X, ⊤))

/-! ### The induced map on ordered Čech cochains -/

/-- The map induced on ordered Čech cochains by a morphism of the underlying abelian sheaves:
apply the morphism on each principal-open intersection. -/
public def ordCochainMap (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (p : ℕ)
    (V : X.Opens) :
    CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i)) (Scheme.Modules.presheaf F) p →+
      CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i))
        (Scheme.Modules.presheaf G) p where
  toFun cc := fun s =>
    sectionsHom ψ (CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) s.1) (cc s)
  map_zero' := by funext s; exact map_zero _
  map_add' cc dd := by funext s; exact map_add _ _ _

/-- **The ordered Čech differential is natural in the coefficient sheaf of abelian groups**, along
a morphism of the underlying abelian sheaves. -/
public theorem ordD_ordCochainMap (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (p : ℕ) (V : X.Opens)
    (cc : CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i))
      (Scheme.Modules.presheaf F) p)
    (t : CechCochains.OrdIndex (I := Fin c) (p + 1)) :
    CechCochains.ordD (fun i => V ⊓ X.basicOpen (f i)) (Scheme.Modules.presheaf G) p
        (ordCochainMap f ψ p V cc) t =
      sectionsHom ψ (CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) t.1)
        (CechCochains.ordD (fun i => V ⊓ X.basicOpen (f i))
          (Scheme.Modules.presheaf F) p cc t) := by
  rw [ordD_apply, ordD_apply,
    map_sum (sectionsHom ψ (CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) t.1))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [AddMonoidHom.map_zsmul]
  congr 1
  rw [restr_eq, restr_eq]
  exact (sectionsHom_naturality ψ
    (homOfLE (CechCochains.inter_le_omit (fun i => V ⊓ X.basicOpen (f i)) t.1 j)) _).symm

/-! ### The induced map on the terms of the Čech complex -/

/-- The map induced on the sections of a positive-degree term of the extended alternating Čech
complex by a morphism of the underlying abelian sheaves.  It is conjugate to `ordCochainMap` by
the identification `secIso` of the sections of the term with the ordered Čech cochains. -/
public def prodTermAbApp (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (p : ℕ)
    (V : X.Opens) : Γ(prodTerm f F p, V) →+ Γ(prodTerm f G p, V) :=
  (secIso f G p V).symm.toAddMonoidHom.comp
    ((ordCochainMap f ψ p V).comp (secIso f F p V).toAddMonoidHom)

/-- The Čech cochain of the image of a section is the image of its Čech cochain. -/
public theorem secIso_prodTermAbApp_eq
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (p : ℕ)
    (V : X.Opens) (x : Γ(prodTerm f F p, V)) :
    secIso f G p V (prodTermAbApp f ψ p V x) = ordCochainMap f ψ p V (secIso f F p V x) :=
  (secIso f G p V).apply_symm_apply _

/-- Each component of the Čech cochain of the image of a section is the image of the
corresponding component of its Čech cochain. -/
public theorem secIso_prodTermAbApp
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (p : ℕ)
    (V : X.Opens) (x : Γ(prodTerm f F p, V)) (s : CechCochains.OrdIndex (I := Fin c) p) :
    secIso f G p V (prodTermAbApp f ψ p V x) s =
      sectionsHom ψ (CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) s.1)
        (secIso f F p V x s) := by
  rw [secIso_prodTermAbApp_eq]
  rfl

/-- The induced map on the sections of a term commutes with restriction of the ambient open. -/
public theorem prodTermAbApp_restrict
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (p : ℕ) {W V : X.Opens} (hWV : W ≤ V) (x : Γ(prodTerm f F p, V)) :
    prodTermAbApp f ψ p W ((prodTerm f F p).presheaf.map (homOfLE hWV).op x) =
      (prodTerm f G p).presheaf.map (homOfLE hWV).op (prodTermAbApp f ψ p V x) := by
  refine (secIso f G p W).injective (funext fun s => ?_)
  rw [secIso_prodTermAbApp, secIso_restrict, secIso_restrict, secIso_prodTermAbApp,
    sectionsHom_naturality]

/-- The morphism of abelian presheaves induced on a positive-degree Čech term. -/
public def prodTermPre (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (p : ℕ) :
    Scheme.Modules.presheaf (prodTerm f F p) ⟶ Scheme.Modules.presheaf (prodTerm f G p) where
  app U := AddCommGrpCat.ofHom (prodTermAbApp f ψ p U.unop)
  naturality U V g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    change prodTermAbApp f ψ p V.unop
        ((prodTerm f F p).presheaf.map (homOfLE (leOfHom g.unop)).op x) =
      (prodTerm f G p).presheaf.map (homOfLE (leOfHom g.unop)).op
        (prodTermAbApp f ψ p U.unop x)
    exact prodTermAbApp_restrict f ψ p (leOfHom g.unop) x

/-- **The morphism of abelian sheaves induced on a positive-degree term of the extended
alternating Čech complex** by a morphism of the underlying abelian sheaves of the coefficient
modules. -/
public def prodTermAb (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (p : ℕ) :
    (abelianSheaf X).obj (prodTerm f F p) ⟶ (abelianSheaf X).obj (prodTerm f G p) :=
  abHom (prodTermPre f ψ p)

/-- The induced map on a positive-degree Čech term, read on sections. -/
public theorem sectionsHom_prodTermPre
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (p : ℕ) (V : X.Opens)
    (x : Γ(prodTerm f F p, V)) :
    sectionsHom (prodTermPre f ψ p) V x = prodTermAbApp f ψ p V x := rfl

/-- The map induced on the sections of an arbitrary term of the extended alternating Čech
complex: the morphism itself in degree `0`, where the term is the coefficient module, and
`prodTermAbApp` in positive degrees. -/
public def termAbApp (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (n : ℕ) → (V : X.Opens) → (Γ(term f F n, V) →+ Γ(term f G n, V))
  | 0, V => sectionsHom ψ V
  | (p + 1), V => prodTermAbApp f ψ p V

/-- The morphism of abelian presheaves induced on an arbitrary Čech term. -/
public def termPre (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (n : ℕ) → (Scheme.Modules.presheaf (term f F n) ⟶ Scheme.Modules.presheaf (term f G n))
  | 0 => ψ
  | (p + 1) => prodTermPre f ψ p

/-- **The morphism of abelian sheaves induced on an arbitrary term of the extended alternating
Čech complex.** -/
public def termAb (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (n : ℕ) :
    (abelianSheaf X).obj (term f F n) ⟶ (abelianSheaf X).obj (term f G n) :=
  abHom (termPre f ψ n)

/-- The induced map on an arbitrary Čech term, read on sections. -/
public theorem sectionsHom_termPre (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (n : ℕ) → (V : X.Opens) → (x : Γ(term f F n, V)) →
      sectionsHom (termPre f ψ n) V x = termAbApp f ψ n V x
  | 0, _, _ => rfl
  | (_ + 1), _, _ => rfl

/-! ### Compatibility with the `𝒪_X`-linear functoriality -/

/-- For a morphism of `𝒪_X`-modules the induced map on the sections of a positive-degree Čech
term is the action on sections of the `𝒪_X`-linear map
`Stacks.Perfect.ExtendedAlternatingCech.prodMap`. -/
public theorem prodTermAbApp_mapPresheaf (φ : F ⟶ G) (p : ℕ) (V : X.Opens)
    (x : Γ(prodTerm f F p, V)) :
    prodTermAbApp f (Scheme.Modules.Hom.mapPresheaf φ) p V x = (prodMap f φ p).app V x := by
  refine (secIso f G p V).injective (funext fun s => ?_)
  rw [secIso_prodTermAbApp, prodMap_section]
  rfl

/-- For a morphism of `𝒪_X`-modules the induced map on a positive-degree Čech term is the
underlying abelian-sheaf morphism of the `𝒪_X`-linear map
`Stacks.Perfect.ExtendedAlternatingCech.prodMap`. -/
public theorem prodTermAb_mapPresheaf (φ : F ⟶ G) (p : ℕ) :
    prodTermAb f (Scheme.Modules.Hom.mapPresheaf φ) p =
      (abelianSheaf X).map (prodMap f φ p) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  exact prodTermAbApp_mapPresheaf f φ p U.unop x

/-- For a morphism of `𝒪_X`-modules the induced map on an arbitrary Čech term is the underlying
abelian-sheaf morphism of the degree-`n` component of the `𝒪_X`-linear chain map
`Stacks.Perfect.ExtendedAlternatingCech.cplxMap`. -/
public theorem termAb_mapPresheaf (φ : F ⟶ G) :
    (n : ℕ) → termAb f (Scheme.Modules.Hom.mapPresheaf φ) n =
      (abelianSheaf X).map ((cplxMap f φ).f n)
  | 0 => rfl
  | (p + 1) => prodTermAb_mapPresheaf f φ p

/-! ### The differentials commute with the induced maps -/

/-- The signed alternating restriction differential commutes with the map induced by a morphism
of the underlying abelian sheaves. -/
public theorem prodTermAbApp_difSucc (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (p : ℕ) (V : X.Opens) (x : Γ(prodTerm f F p, V)) :
    prodTermAbApp f ψ (p + 1) V ((difSucc f F p).app V x) =
      (difSucc f G p).app V (prodTermAbApp f ψ p V x) := by
  refine (secIso f G (p + 1) V).injective (funext fun t => ?_)
  rw [secIso_prodTermAbApp, secIso_difSucc, secIso_difSucc, secIso_prodTermAbApp_eq,
    ordD_ordCochainMap]

/-- The augmentation out of degree `0` commutes with the map induced by a morphism of the
underlying abelian sheaves. -/
public theorem prodTermAbApp_difZero (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (V : X.Opens) (x : Γ(F, V)) :
    prodTermAbApp f ψ 0 V ((difZero f F).app V x) =
      (difZero f G).app V (sectionsHom ψ V x) := by
  refine (secIso f G 0 V).injective (funext fun s => ?_)
  rw [secIso_prodTermAbApp, secIso_difZero, secIso_difZero, sectionsHom_naturality]

end Terms

/-! ### The last differential and its cokernel -/

section LastDif

variable {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))

/-- **The last differential of the extended alternating Čech complex commutes with the map
induced by a morphism of the underlying abelian sheaves**, sectionwise. -/
public theorem termAbApp_lastDif (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (V : X.Opens) (x : Γ(term f F d, V)) :
    prodTermAbApp f ψ d V ((lastDif f F).app V x) =
      (lastDif f G).app V (termAbApp f ψ d V x) := by
  cases d with
  | zero =>
      rw [lastDif_zero, lastDif_zero]
      exact prodTermAbApp_difZero f ψ V x
  | succ e =>
      rw [lastDif_succ, lastDif_succ]
      exact prodTermAbApp_difSucc f ψ e V x

/-- **The naturality square of the last differential, in sheaves of abelian groups.**  For every
morphism `ψ` of the underlying abelian sheaves of the coefficient modules — in particular for one
that is not `𝒪_X`-linear — the square formed by the two last differentials and the two induced
maps on the Čech terms commutes. -/
public theorem termPre_lastDif (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (V : X.Opens) (x : Γ(term f F d, V)) :
    prodTermAbApp f ψ d V ((lastDif f F).app V x) =
      (lastDif f G).app V (sectionsHom (termPre f ψ d) V x) := by
  rw [sectionsHom_termPre]
  exact termAbApp_lastDif f ψ V x

/-- **The naturality square of the last differential, in sheaves of abelian groups.**  For every
morphism `ψ` of the underlying abelian sheaves of the coefficient modules — in particular for one
that is not `𝒪_X`-linear — the square formed by the two last differentials and the two induced
maps on the Čech terms commutes. -/
public theorem map_lastDif_comp_prodTermAb
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).map (lastDif f F) ≫ prodTermAb f ψ d =
      termAb f ψ d ≫ (abelianSheaf X).map (lastDif f G) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  exact termPre_lastDif f ψ U.unop x

/-- **The morphism induced on the elementary Čech cokernel of [Stacks, Tag 0G7Q] by a morphism of
the underlying abelian sheaves.**  This is the abelian functoriality of

`Coker(⨁ᵢ ℱ_{1…î…c} ⟶ ℱ_{1…c})`,

the module in which the class map of [Stacks, Tag 0G7Q] takes its values: the map of cokernels
induced by the naturality square `map_lastDif_comp_prodTermAb`, read through the identification
of the underlying abelian sheaf of a cokernel with the cokernel of the underlying morphism. -/
public def cokernelLastDifAb (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).obj (cokernel (lastDif f F)) ⟶
      (abelianSheaf X).obj (cokernel (lastDif f G)) :=
  (PreservesCokernel.iso (abelianSheaf X) (lastDif f F)).hom ≫
    cokernel.map ((abelianSheaf X).map (lastDif f F)) ((abelianSheaf X).map (lastDif f G))
      (termAb f ψ d) (prodTermAb f ψ d) (map_lastDif_comp_prodTermAb f ψ) ≫
    (PreservesCokernel.iso (abelianSheaf X) (lastDif f G)).inv

/-- **The defining property of `cokernelLastDifAb`**: it is compatible with the canonical
epimorphisms onto the two cokernels.  Read on the class of a top-degree Čech cochain `σ`, it says
that the morphism sends `[σ]` to `[ψ(σ)]`. -/
public theorem map_cokernelπ_comp_cokernelLastDifAb
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).map (cokernel.π (lastDif f F)) ≫ cokernelLastDifAb f ψ =
      prodTermAb f ψ d ≫ (abelianSheaf X).map (cokernel.π (lastDif f G)) := by
  rw [cokernelLastDifAb, ← Category.assoc, ← Category.assoc,
    PreservesCokernel.π_iso_hom (abelianSheaf X) (lastDif f F), cokernel.π_desc,
    Category.assoc, PreservesCokernel.iso_inv, π_comp_cokernelComparison]

/-- The canonical epimorphism onto the Čech cokernel stays an epimorphism after forgetting the
module structure. -/
public instance epi_map_cokernelπ_lastDif :
    Epi ((abelianSheaf X).map (cokernel.π (lastDif f F))) := by
  have h : (abelianSheaf X).map (cokernel.π (lastDif f F)) =
      cokernel.π ((abelianSheaf X).map (lastDif f F)) ≫
        (PreservesCokernel.iso (abelianSheaf X) (lastDif f F)).inv := by
    rw [← PreservesCokernel.π_iso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- **`cokernelLastDifAb` is the unique morphism compatible with the canonical epimorphisms onto
the two cokernels.** -/
public theorem cokernelLastDifAb_unique
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (u : (abelianSheaf X).obj (cokernel (lastDif f F)) ⟶
      (abelianSheaf X).obj (cokernel (lastDif f G)))
    (hu : (abelianSheaf X).map (cokernel.π (lastDif f F)) ≫ u =
      prodTermAb f ψ d ≫ (abelianSheaf X).map (cokernel.π (lastDif f G))) :
    u = cokernelLastDifAb f ψ :=
  (cancel_epi ((abelianSheaf X).map (cokernel.π (lastDif f F)))).mp
    (hu.trans (map_cokernelπ_comp_cokernelLastDifAb f ψ).symm)

/-- The abelian functoriality of the Čech cokernel sends the identity to the identity. -/
public theorem cokernelLastDifAb_id :
    cokernelLastDifAb f (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) = 𝟙 _ := by
  refine (cokernelLastDifAb_unique f _ (𝟙 _) ?_).symm
  rw [Category.comp_id, prodTermAb_mapPresheaf, prodMap_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end LastDif

end Stacks.Perfect.AbelianFraction

end
