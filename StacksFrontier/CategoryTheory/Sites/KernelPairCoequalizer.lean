module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute

/-!
# A locally surjective map of sheaves of sets presents its target as a coequalizer

Let `φ : U ⟶ F` be a morphism of sheaves of sets on a site, and let `s, t : R ⟶ U` be a pair
of morphisms which realises the *kernel pair* of `φ` pointwise: whenever two sections of `U`
over an object `V` have the same image under `φ`, they are the `s`- and `t`-images of a single
section of `R` over `V`. If moreover `φ` is locally surjective, then `φ` exhibits `F` as the
coequalizer of `s` and `t`.

The descent morphism `F ⟶ c.pt` out of a cofork `c` is built sectionwise: a section `ξ` of `F`
over `T` is locally in the image of `φ`, so choosing local lifts and pushing them into `c.pt`
gives a compatible family, which amalgamates because `c.pt` is a sheaf. The amalgamation does
not depend on the chosen lifts, because two lifts agreeing after `φ` are related by a section
of `R`, and `c.π` coequalizes `s` and `t`. Uniqueness of the amalgamation and of the descent
morphism are both instances of sheaf separatedness.

## Main results

* `CategoryTheory.Sheaf.isColimitCoforkOfKernelPair`: the cofork on a locally surjective `φ`
  whose kernel pair is realised by `s, t` is a colimit.

## Implementation notes

The statement is universe-polymorphic in all three of the objects of the site, its morphisms
and the values of the sheaves, and it never forms a limit in the category of sheaves: the
kernel pair enters only through the pointwise hypothesis `hker`. Both points are needed for
the big fppf site of a scheme, whose objects and morphisms live in different universes and
whose sheaves of sets take values in the universe of morphisms. The special case where `R` is
the actual fibre product `U ×_F U` of sheaves valued in `Type (max v u)` is Tag 086K, proved
separately as `coequalizer_of_surjection`; it is not general enough to apply to the big fppf
site, and a later pass should re-derive it from this result.

## References

* [Stacks Project, Tag 086K](https://stacks.math.columbia.edu/tag/086K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Two sections of a sheaf of sets over `T` which agree after restriction along every
morphism of a covering sieve of `T` are equal. -/
theorem eq_of_eq_on_sieve {X : Sheaf J (Type w)} {T : C} {S : Sieve T} (hS : S ∈ J T)
    (x y : X.obj.obj (op T))
    (h : ∀ ⦃W : C⦄ (k : W ⟶ T), S k → X.obj.map k.op x = X.obj.map k.op y) :
    x = y :=
  (((isSheaf_iff_isSheaf_of_type J X.obj).mp X.property S hS).isSeparatedFor).ext
    fun _ k hk ↦ h k hk

variable {R U F : Sheaf J (Type w)}

/-- The local lifts provided by local surjectivity, read as a covering sieve along which the
given section of the target is in the image. -/
private theorem exists_sieve_of_isLocallySurjective {φ : U ⟶ F}
    (hφ : Presheaf.IsLocallySurjective J φ.hom) {T : C} (ξ : F.obj.obj (op T)) :
    ∃ S : Sieve T, S ∈ J T ∧ ∀ ⦃W : C⦄ (k : W ⟶ T), S k →
      ∃ η : U.obj.obj (op W), φ.hom.app (op W) η = F.obj.map k.op ξ :=
  ⟨Presheaf.imageSieve φ.hom ξ, hφ.imageSieve_mem ξ,
    fun _ _ ⟨η, hη⟩ ↦ ⟨η, by simpa using hη⟩⟩

/-- Two local lifts of a section `ξ` along `g ≫ k` and `k` have the same image under `φ`, once the
first is restricted along `g`. -/
private theorem app_eq_map_of_lifts {φ : U ⟶ F} {T W V : C} {ξ : F.obj.obj (op T)}
    {k : W ⟶ T} {g : V ⟶ W} {a : U.obj.obj (op V)} {b : U.obj.obj (op W)}
    (ha : φ.hom.app (op V) a = F.obj.map (g ≫ k).op ξ)
    (hb : φ.hom.app (op W) b = F.obj.map k.op ξ) :
    φ.hom.app (op V) a = φ.hom.app (op V) (U.obj.map g.op b) := by
  rw [ha, NatTrans.naturality_apply φ.hom g.op b, hb, ← Functor.map_comp_apply]
  rfl

/-- Any cofork on `s` and `t` identifies two sections of `U` with the same image under `φ`,
because such a pair of sections is related by a section of `R`. -/
private theorem cofork_app_eq_of_app_eq (s t : R ⟶ U) (φ : U ⟶ F)
    (hker : ∀ ⦃V : C⦄ (x y : U.obj.obj (op V)),
      φ.hom.app (op V) x = φ.hom.app (op V) y →
      ∃ r : R.obj.obj (op V), s.hom.app (op V) r = x ∧ t.hom.app (op V) r = y)
    (c : Cofork s t) {V : C} {x y : U.obj.obj (op V)}
    (heq : φ.hom.app (op V) x = φ.hom.app (op V) y) :
    c.π.hom.app (op V) x = c.π.hom.app (op V) y := by
  obtain ⟨r, rfl, rfl⟩ := hker x y heq
  exact show (s ≫ c.π).hom.app (op V) r = (t ≫ c.π).hom.app (op V) r by rw [c.condition]

/-- The images in `c.pt` of a family of local lifts of a section `ξ` of `F` form a compatible
family, hence amalgamate to a section of `c.pt`. -/
private theorem exists_amalgamation (s t : R ⟶ U) (φ : U ⟶ F)
    (hker : ∀ ⦃V : C⦄ (x y : U.obj.obj (op V)),
      φ.hom.app (op V) x = φ.hom.app (op V) y →
      ∃ r : R.obj.obj (op V), s.hom.app (op V) r = x ∧ t.hom.app (op V) r = y)
    (c : Cofork s t) {T : C} (ξ : F.obj.obj (op T)) (S : Sieve T) (hS : S ∈ J T)
    (a : ∀ ⦃W : C⦄ (k : W ⟶ T), S k → U.obj.obj (op W))
    (ha : ∀ ⦃W : C⦄ (k : W ⟶ T) (hk : S k),
      φ.hom.app (op W) (a k hk) = F.obj.map k.op ξ) :
    ∃ x : c.pt.obj.obj (op T),
      ∀ ⦃W : C⦄ (k : W ⟶ T) (hk : S k),
        c.pt.obj.map k.op x = c.π.hom.app (op W) (a k hk) := by
  let fam : Presieve.FamilyOfElements c.pt.obj S.arrows :=
    fun _ k hk ↦ c.π.hom.app (op _) (a k hk)
  have hcompat : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W k g hk
    have hnat : c.π.hom.app (op W) (U.obj.map (op g) (a k hk)) =
        c.pt.obj.map (op g) (c.π.hom.app (op V) (a k hk)) :=
      NatTrans.naturality_apply c.π.hom (op g) (a k hk)
    show c.π.hom.app (op W) (a (g ≫ k) (S.downward_closed hk g)) =
      c.pt.obj.map (op g) (c.π.hom.app (op V) (a k hk))
    rw [← hnat]
    apply cofork_app_eq_of_app_eq s t φ hker c
    exact app_eq_map_of_lifts (ha (g ≫ k) (S.downward_closed hk g)) (ha k hk)
  obtain ⟨x, hx, _⟩ := Presheaf.IsSheaf.isSheafFor c.pt.property S hS fam hcompat
  exact ⟨x, fun _ k hk ↦ hx k hk⟩

/-- An amalgamation of the images of one family of local lifts agrees with the image of
*every* local lift, over every object of the site. -/
private theorem map_eq_of_app_eq (s t : R ⟶ U) (φ : U ⟶ F)
    (hker : ∀ ⦃V : C⦄ (x y : U.obj.obj (op V)),
      φ.hom.app (op V) x = φ.hom.app (op V) y →
      ∃ r : R.obj.obj (op V), s.hom.app (op V) r = x ∧ t.hom.app (op V) r = y)
    (c : Cofork s t) {T : C} (ξ : F.obj.obj (op T)) (S : Sieve T) (hS : S ∈ J T)
    (a : ∀ ⦃W : C⦄ (k : W ⟶ T), S k → U.obj.obj (op W))
    (ha : ∀ ⦃W : C⦄ (k : W ⟶ T) (hk : S k),
      φ.hom.app (op W) (a k hk) = F.obj.map k.op ξ)
    (x : c.pt.obj.obj (op T))
    (hx : ∀ ⦃W : C⦄ (k : W ⟶ T) (hk : S k),
      c.pt.obj.map k.op x = c.π.hom.app (op W) (a k hk)) :
    ∀ ⦃W : C⦄ (k : W ⟶ T) (b : U.obj.obj (op W)),
      φ.hom.app (op W) b = F.obj.map k.op ξ →
      c.pt.obj.map k.op x = c.π.hom.app (op W) b := by
  intro W k b hb
  apply eq_of_eq_on_sieve (J := J) (J.pullback_stable k hS)
  intro V g hg
  have lhs : c.pt.obj.map g.op (c.pt.obj.map k.op x) = c.pt.obj.map (g ≫ k).op x := by
    rw [← Functor.map_comp_apply]
    rfl
  have rhs : c.pt.obj.map g.op (c.π.hom.app (op W) b) =
      c.π.hom.app (op V) (U.obj.map g.op b) :=
    (NatTrans.naturality_apply c.π.hom g.op b).symm
  rw [lhs, hx (g ≫ k) hg, rhs, cofork_app_eq_of_app_eq s t φ hker c
    (app_eq_map_of_lifts (ha (g ≫ k) hg) hb)]

/-- Every section of `F` descends to a section of the point of a cofork, compatibly with all
local lifts. -/
private theorem exists_descSection (s t : R ⟶ U) (φ : U ⟶ F)
    (hker : ∀ ⦃V : C⦄ (x y : U.obj.obj (op V)),
      φ.hom.app (op V) x = φ.hom.app (op V) y →
      ∃ r : R.obj.obj (op V), s.hom.app (op V) r = x ∧ t.hom.app (op V) r = y)
    (hφ : Presheaf.IsLocallySurjective J φ.hom) (c : Cofork s t)
    (T : C) (ξ : F.obj.obj (op T)) :
    ∃ x : c.pt.obj.obj (op T),
      ∀ ⦃W : C⦄ (k : W ⟶ T) (b : U.obj.obj (op W)),
        φ.hom.app (op W) b = F.obj.map k.op ξ →
        c.pt.obj.map k.op x = c.π.hom.app (op W) b := by
  obtain ⟨S, hS, hlift⟩ := exists_sieve_of_isLocallySurjective hφ ξ
  choose a ha using hlift
  obtain ⟨x, hx⟩ := exists_amalgamation s t φ hker c ξ S hS a ha
  exact ⟨x, map_eq_of_app_eq s t φ hker c ξ S hS a ha x hx⟩

/-- The descended section is unique. -/
private theorem descSection_unique (s t : R ⟶ U) (φ : U ⟶ F)
    (hφ : Presheaf.IsLocallySurjective J φ.hom) (c : Cofork s t)
    {T : C} (ξ : F.obj.obj (op T)) {x y : c.pt.obj.obj (op T)}
    (hx : ∀ ⦃W : C⦄ (k : W ⟶ T) (b : U.obj.obj (op W)),
      φ.hom.app (op W) b = F.obj.map k.op ξ →
      c.pt.obj.map k.op x = c.π.hom.app (op W) b)
    (hy : ∀ ⦃W : C⦄ (k : W ⟶ T) (b : U.obj.obj (op W)),
      φ.hom.app (op W) b = F.obj.map k.op ξ →
      c.pt.obj.map k.op y = c.π.hom.app (op W) b) :
    x = y := by
  obtain ⟨S, hS, hlift⟩ := exists_sieve_of_isLocallySurjective hφ ξ
  apply eq_of_eq_on_sieve (J := J) hS x y
  intro W k hk
  obtain ⟨b, hb⟩ := hlift k hk
  rw [hx k b hb, hy k b hb]

/-- The descended sections assemble into a morphism of sheaves through which `φ` factors the
projection of a cofork. -/
private theorem exists_descent (s t : R ⟶ U) (φ : U ⟶ F)
    (hker : ∀ ⦃V : C⦄ (x y : U.obj.obj (op V)),
      φ.hom.app (op V) x = φ.hom.app (op V) y →
      ∃ r : R.obj.obj (op V), s.hom.app (op V) r = x ∧ t.hom.app (op V) r = y)
    (hφ : Presheaf.IsLocallySurjective J φ.hom) (c : Cofork s t) :
    ∃ m : F ⟶ c.pt, φ ≫ m = c.π := by
  choose desc desc_spec using exists_descSection s t φ hker hφ c
  have hnat : ∀ ⦃X Y : Cᵒᵖ⦄ (k : X ⟶ Y) (ξ : F.obj.obj X),
      desc Y.unop (F.obj.map k ξ) = c.pt.obj.map k (desc X.unop ξ) := by
    intro X Y k ξ
    apply descSection_unique s t φ hφ c (F.obj.map k ξ) (desc_spec Y.unop (F.obj.map k ξ))
    intro W g b hb
    have hcomp : φ.hom.app (op W) b = F.obj.map (op ((k ≫ g.op).unop)) ξ := by
      rw [show op ((k ≫ g.op).unop) = k ≫ g.op from Quiver.Hom.op_unop _,
        Functor.map_comp_apply]
      exact hb
    show c.pt.obj.map g.op (c.pt.obj.map k (desc X.unop ξ)) = _
    rw [← Functor.map_comp_apply]
    exact desc_spec X.unop ξ ((k ≫ g.op).unop) b hcomp
  refine ⟨⟨{ app := fun X ↦ ↾(fun ξ ↦ desc X.unop ξ), naturality := ?_ }⟩, ?_⟩
  · intro X Y k
    ext ξ
    exact hnat k ξ
  · ext X ξ
    have hId : (𝟙 X.unop).op = 𝟙 X := op_id_unop
    have hφid : φ.hom.app X ξ = F.obj.map (𝟙 X.unop).op (φ.hom.app X ξ) := by
      rw [hId, Functor.map_id_apply]
    have h := desc_spec X.unop (φ.hom.app X ξ) (𝟙 X.unop) ξ hφid
    rwa [hId, Functor.map_id_apply] at h

/-- The factorisation of the projection of a cofork through `φ` is unique. -/
private theorem descent_unique (s t : R ⟶ U) (φ : U ⟶ F)
    (hφ : Presheaf.IsLocallySurjective J φ.hom) (c : Cofork s t)
    (m₁ m₂ : F ⟶ c.pt) (h₁ : φ ≫ m₁ = c.π) (h₂ : φ ≫ m₂ = c.π) : m₁ = m₂ := by
  apply Sheaf.hom_ext
  ext ⟨T⟩ : 2
  apply ConcreteCategory.ext
  ext ξ
  simp only [TypeCat.Fun.toFun_apply]
  have key (m : F ⟶ c.pt) (hm : φ ≫ m = c.π) ⦃W : C⦄ (k : W ⟶ T) (b : U.obj.obj (op W))
      (hb : φ.hom.app (op W) b = F.obj.map k.op ξ) :
      c.pt.obj.map k.op (m.hom.app (op T) ξ) = c.π.hom.app (op W) b :=
    calc
      c.pt.obj.map k.op (m.hom.app (op T) ξ) = m.hom.app (op W) (F.obj.map k.op ξ) :=
        (NatTrans.naturality_apply m.hom k.op ξ).symm
      _ = c.π.hom.app (op W) b := by
        rw [← hb]
        simpa using congrArg (fun η : U ⟶ c.pt ↦ η.hom.app (op W) b) hm
  exact descSection_unique s t φ hφ c ξ (key m₁ h₁) (key m₂ h₂)

/-- A locally surjective morphism `φ : U ⟶ F` of sheaves of sets whose kernel pair is realised
pointwise by `s, t : R ⟶ U` exhibits `F` as the coequalizer of `s` and `t`. -/
theorem nonempty_isColimitCoforkOfKernelPair (s t : R ⟶ U) (φ : U ⟶ F)
    (hcondition : s ≫ φ = t ≫ φ)
    (hker : ∀ ⦃V : C⦄ (x y : U.obj.obj (op V)),
      φ.hom.app (op V) x = φ.hom.app (op V) y →
      ∃ r : R.obj.obj (op V), s.hom.app (op V) r = x ∧ t.hom.app (op V) r = y)
    (hφ : Presheaf.IsLocallySurjective J φ.hom) :
    Nonempty (IsColimit (Cofork.ofπ φ hcondition)) := by
  refine ⟨Cofork.IsColimit.mk' _ fun c ↦ ?_⟩
  let hdesc := exists_descent s t φ hker hφ c
  refine ⟨hdesc.choose, ?_, ?_⟩
  · simpa only [Cofork.π_ofπ] using hdesc.choose_spec
  · intro m hm
    exact descent_unique s t φ hφ c m hdesc.choose
      (by simpa only [Cofork.π_ofπ] using hm)
      (by simpa only [Cofork.π_ofπ] using hdesc.choose_spec)

/-- The colimit structure on the cofork of
`CategoryTheory.Sheaf.nonempty_isColimitCoforkOfKernelPair`, chosen once and for all. -/
noncomputable def isColimitCoforkOfKernelPair (s t : R ⟶ U) (φ : U ⟶ F)
    (hcondition : s ≫ φ = t ≫ φ)
    (hker : ∀ ⦃V : C⦄ (x y : U.obj.obj (op V)),
      φ.hom.app (op V) x = φ.hom.app (op V) y →
      ∃ r : R.obj.obj (op V), s.hom.app (op V) r = x ∧ t.hom.app (op V) r = y)
    (hφ : Presheaf.IsLocallySurjective J φ.hom) :
    IsColimit (Cofork.ofπ φ hcondition) :=
  Classical.choice (nonempty_isColimitCoforkOfKernelPair s t φ hcondition hker hφ)

end CategoryTheory.Sheaf

end
